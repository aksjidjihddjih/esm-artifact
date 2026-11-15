//! Host driver for the `esm-guest` rv32im ELF: request encoding, execution in the emulator, result decoding.
pub mod emu;

use emu::Emu;

pub const INPUT: u32 = 0x0E00_0000;
pub const OUTPUT: u32 = 0x0F00_0000;

pub struct Case1 {
    pub prog: u32,
    pub args: Vec<u32>,
    pub j: u64,
    pub width: u32,
    pub delta: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Out1 {
    pub ok: u32,
    pub steps: u32,
    pub value: u64,
    pub instret: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Out2 {
    pub eq: u32,
    pub status: u32,
    pub kam: u32,
    pub beta: u32,
    pub nodes: u32,
    pub work: u32,
    pub instret: u64,
}

pub struct Run<T> {
    pub results: Vec<T>,
    pub exit: u32,
    pub total_instret: u64,
    pub guest_total_instret: u64,
    pub heap_high_water: u32,
}

fn put(v: &mut Vec<u8>, x: u32) {
    v.extend_from_slice(&x.to_le_bytes());
}

fn put_progs(v: &mut Vec<u8>, progs: &[Vec<u8>]) {
    put(v, progs.len() as u32);
    for p in progs {
        put(v, p.len() as u32);
        v.extend_from_slice(p);
        while v.len() % 4 != 0 {
            v.push(0);
        }
    }
}

pub fn encode_mode1(progs: &[Vec<u8>], cases: &[Case1]) -> Vec<u8> {
    let mut v = Vec::new();
    put(&mut v, 1);
    put_progs(&mut v, progs);
    put(&mut v, cases.len() as u32);
    for c in cases {
        put(&mut v, c.prog);
        put(&mut v, c.args.len() as u32);
        for &a in &c.args {
            put(&mut v, a);
        }
        put(&mut v, c.j as u32);
        put(&mut v, (c.j >> 32) as u32);
        put(&mut v, c.width);
        put(&mut v, c.delta);
    }
    v
}

pub fn encode_mode2(progs: &[Vec<u8>], cases: &[(u32, u32, u32, u32)]) -> Vec<u8> {
    let mut v = Vec::new();
    put(&mut v, 2);
    put_progs(&mut v, progs);
    put(&mut v, cases.len() as u32);
    for &(a, b, c, d) in cases {
        for x in [a, b, c, d] {
            put(&mut v, x);
        }
    }
    v
}

fn execute(elf: &[u8], input: &[u8], max_instr: u64) -> Result<Emu, String> {
    let mut e = Emu::load_elf(elf)?;
    if input.len() > 0x0100_0000 {
        return Err("input larger than 16 MiB".into());
    }
    e.write_mem(INPUT, input);
    let code = e.run(max_instr)?;
    if code != 0 || e.read_u32(OUTPUT) != 0x4553_4D31 {
        return Err(format!("guest failed: exit {code}, magic {:#x}", e.read_u32(OUTPUT)));
    }
    Ok(e)
}

pub fn run_mode1(elf: &[u8], progs: &[Vec<u8>], cases: &[Case1], max_instr: u64) -> Result<Run<Out1>, String> {
    let e = execute(elf, &encode_mode1(progs, cases), max_instr)?;
    let mut results = Vec::new();
    for i in 0..cases.len() as u32 {
        let o = OUTPUT + 24 + i * 24;
        let w: Vec<u32> = (0..6).map(|k| e.read_u32(o + 4 * k)).collect();
        results.push(Out1 { ok: w[0], steps: w[1], value: ((w[3] as u64) << 32) | w[2] as u64, instret: ((w[5] as u64) << 32) | w[4] as u64 });
    }
    Ok(Run {
        results,
        exit: 0,
        total_instret: e.instret,
        guest_total_instret: ((e.read_u32(OUTPUT + 20) as u64) << 32) | e.read_u32(OUTPUT + 16) as u64,
        heap_high_water: e.read_u32(OUTPUT + 12),
    })
}

pub fn run_mode2(elf: &[u8], progs: &[Vec<u8>], cases: &[(u32, u32, u32, u32)], max_instr: u64) -> Result<Run<Out2>, String> {
    let e = execute(elf, &encode_mode2(progs, cases), max_instr)?;
    let mut results = Vec::new();
    for i in 0..cases.len() as u32 {
        let o = OUTPUT + 24 + i * 48;
        let w: Vec<u32> = (0..8).map(|k| e.read_u32(o + 4 * k)).collect();
        results.push(Out2 { eq: w[0], status: w[1], kam: w[2], beta: w[3], nodes: w[4], work: w[5], instret: ((w[7] as u64) << 32) | w[6] as u64 });
    }
    Ok(Run {
        results,
        exit: 0,
        total_instret: e.instret,
        guest_total_instret: ((e.read_u32(OUTPUT + 20) as u64) << 32) | e.read_u32(OUTPUT + 16) as u64,
        heap_high_water: e.read_u32(OUTPUT + 12),
    })
}

pub fn guest_elf_path() -> String {
    std::env::var("ESM_GUEST_ELF").unwrap_or_else(|_| concat!(env!("CARGO_MANIFEST_DIR"), "/../esm-guest/target/riscv32im-unknown-none-elf/release/esm-guest").to_string())
}

pub fn load_guest() -> Vec<u8> {
    std::fs::read(guest_elf_path()).expect("guest ELF missing: build esm-guest first")
}
