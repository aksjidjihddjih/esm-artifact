//! rv32im guest: the program a zkVM would prove.  Reads a request from `INPUT`, runs `esm-core`, writes the result to `OUTPUT`.
//!
//! mode 1 (batch run):  nprogs, {len, bits...}*, ncases, {prog, nargs, arg_prog*, j_lo, j_hi, width, delta}*
//!         -> per case 6 words  [ok, steps, value_lo, value_hi, instret_lo, instret_hi]
//! mode 2 (T6 check):   nprogs, {len, bits...}*, ncases, {p_s, q, p_i, fuel_max}*
//!         -> per case 12 words [eq(0/1/2), status, kam, beta, nodes, work, instret_lo, instret_hi, 0, 0, 0, 0]
//! header (written last): [magic, mode, ncases, heap_high_water, total_instret_lo, total_instret_hi]
#![no_std]
#![no_main]
#![allow(static_mut_refs)]

extern crate alloc;

use alloc::vec::Vec;
use core::alloc::{GlobalAlloc, Layout};
use core::arch::{asm, global_asm};
use core::ptr::{null_mut, read, write};

use esm_core::bohm::{t6_check, T6Status};
use esm_core::blc::{parse_blc, Arena};
use esm_core::kam::run_bits_total;

const INPUT: u32 = 0x0E00_0000;
const OUTPUT: u32 = 0x0F00_0000;
const HEAP_END: usize = 0x0E00_0000;
const MAGIC: u32 = 0x4553_4D31;

global_asm!(
    r#"
    .section .text.init
    .globl _start
_start:
    la sp, _stack_top
    call rust_main
    li a7, 93
    ecall
1:  j 1b
"#
);

extern "C" {
    static _heap_start: u8;
}

// ---- size-class free-list allocator (deterministic; 16-byte aligned power-of-two blocks)
struct Alloc;
static mut BUMP: usize = 0;
static mut FREE: [usize; 28] = [0; 28];
static mut HIGH: usize = 0;

fn class(size: usize) -> usize {
    let s = if size < 16 { 16 } else { size };
    s.next_power_of_two().trailing_zeros() as usize
}

unsafe impl GlobalAlloc for Alloc {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 {
        if l.align() > 16 {
            return null_mut();
        }
        let c = class(l.size());
        if c >= 28 {
            return null_mut();
        }
        let head = FREE[c];
        if head != 0 {
            FREE[c] = read(head as *const usize);
            return head as *mut u8;
        }
        if BUMP == 0 {
            BUMP = (&_heap_start as *const u8 as usize + 15) & !15;
        }
        let sz = 1usize << c;
        let p = BUMP;
        if p + sz > HEAP_END {
            return null_mut();
        }
        BUMP = p + sz;
        let used = BUMP - (&_heap_start as *const u8 as usize);
        if used > HIGH {
            HIGH = used;
        }
        p as *mut u8
    }
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) {
        let c = class(l.size());
        write(p as *mut usize, FREE[c]);
        FREE[c] = p as usize;
    }
}

#[global_allocator]
static A: Alloc = Alloc;

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    unsafe {
        write(OUTPUT as *mut u32, 0xDEAD_0001);
        asm!("li a7, 93", "li a0, 101", "ecall", options(noreturn));
    }
}

fn instret() -> u64 {
    let (lo, hi, hi2): (u32, u32, u32);
    unsafe {
        asm!("rdinstreth {0}", out(reg) hi);
        asm!("rdinstret {0}", out(reg) lo);
        asm!("rdinstreth {0}", out(reg) hi2);
    }
    let _ = hi2;
    ((hi as u64) << 32) | lo as u64
}

struct Rd(u32);
impl Rd {
    fn u32(&mut self) -> u32 {
        let v = unsafe { read(self.0 as *const u32) };
        self.0 += 4;
        v
    }
    fn bits(&mut self, n: u32) -> Vec<u8> {
        let mut v = Vec::with_capacity(n as usize);
        for i in 0..n {
            v.push(unsafe { read((self.0 + i) as *const u8) });
        }
        self.0 += (n + 3) & !3;
        v
    }
}

struct Wr(u32);
impl Wr {
    fn u32(&mut self, v: u32) {
        unsafe { write(self.0 as *mut u32, v) };
        self.0 += 4;
    }
}

#[no_mangle]
pub extern "C" fn rust_main() -> u32 {
    let t_start = instret();
    let mut r = Rd(INPUT);
    let mode = r.u32();
    let nprogs = r.u32();
    let mut progs: Vec<Vec<u8>> = Vec::new();
    for _ in 0..nprogs {
        let len = r.u32();
        progs.push(r.bits(len));
    }
    let ncases = r.u32();
    let mut w = Wr(OUTPUT + 24);
    for _ in 0..ncases {
        let t0 = instret();
        if mode == 1 {
            let pi = r.u32() as usize;
            let nargs = r.u32();
            let mut args: Vec<usize> = Vec::new();
            for _ in 0..nargs {
                args.push(r.u32() as usize);
            }
            let (j_lo, j_hi, width, delta) = (r.u32(), r.u32(), r.u32(), r.u32());
            let arg_refs: Vec<&[u8]> = args.iter().map(|&i| progs[i].as_slice()).collect();
            let mut arena = Arena::new_plain();
            let j = ((j_hi as u64) << 32) | j_lo as u64;
            let (ok, steps, lo, hi) = match run_bits_total(&mut arena, &progs[pi], &arg_refs, j, width, delta as u64) {
                Ok(o) => {
                    let v = o.value.to_u64().unwrap_or(u64::MAX);
                    (o.ok as u32, o.steps as u32, v as u32, (v >> 32) as u32)
                }
                Err(_) => (2, 0, 0, 0),
            };
            let dt = instret() - t0;
            for x in [ok, steps, lo, hi, dt as u32, (dt >> 32) as u32] {
                w.u32(x);
            }
        } else {
            let (ips, iq, ipi, fuel) = (r.u32() as usize, r.u32() as usize, r.u32() as usize, r.u32());
            let mut arena = Arena::new_interned();
            let ps = parse_blc(&mut arena, &progs[ips]);
            let q = parse_blc(&mut arena, &progs[iq]);
            let pi = parse_blc(&mut arena, &progs[ipi]);
            let mut out = [3u32, 9, 0, 0, 0, 0];
            if let (Ok(ps), Ok(q), Ok(pi)) = (ps, q, pi) {
                if let Ok(res) = t6_check(&mut arena, ps, q, pi, fuel as u64) {
                    out = [
                        match res.eq {
                            Some(false) => 0,
                            Some(true) => 1,
                            None => 2,
                        },
                        match res.status {
                            T6Status::Equal => 0,
                            T6Status::NotEqual => 1,
                            T6Status::FuelExhausted => 2,
                            T6Status::ResourceLimit => 3,
                        },
                        res.fuel.kam as u32,
                        res.fuel.beta as u32,
                        res.fuel.nodes as u32,
                        res.fuel.work as u32,
                    ];
                }
            }
            let dt = instret() - t0;
            for x in out {
                w.u32(x);
            }
            for x in [dt as u32, (dt >> 32) as u32, 0, 0, 0, 0] {
                w.u32(x);
            }
        }
    }
    let total = instret() - t_start;
    let mut h = Wr(OUTPUT);
    for x in [MAGIC, mode, ncases, unsafe { HIGH } as u32, total as u32, (total >> 32) as u32] {
        h.u32(x);
    }
    0
}
