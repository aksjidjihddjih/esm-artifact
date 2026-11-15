//! Minimal RV32IM interpreter (no C/A/F extensions, machine mode, flat 256 MiB RAM).
//! `instret` counts retired instructions: for a zkVM such as SP1 / RISC Zero this is the first-order proxy of the
//! trace length ("cycles"). Precompile syscalls (keccak, sha256, ...) are NOT modelled.

pub const MEM_SIZE: usize = 0x1000_0000;

pub struct Emu {
    pub mem: Vec<u8>,
    pub regs: [u32; 32],
    pub pc: u32,
    pub instret: u64,
}

fn sx(v: u32, bits: u32) -> u32 {
    let s = 32 - bits;
    (((v << s) as i32) >> s) as u32
}

impl Emu {
    pub fn load_elf(elf: &[u8]) -> Result<Emu, String> {
        if elf.len() < 52 || &elf[0..4] != b"\x7fELF" || elf[4] != 1 || elf[5] != 1 {
            return Err("not an ELF32 little-endian file".into());
        }
        let u16at = |o: usize| u16::from_le_bytes([elf[o], elf[o + 1]]) as usize;
        let u32at = |o: usize| u32::from_le_bytes([elf[o], elf[o + 1], elf[o + 2], elf[o + 3]]);
        if u16at(18) != 0xF3 {
            return Err("not a RISC-V ELF".into());
        }
        let entry = u32at(24);
        let (phoff, phentsize, phnum) = (u32at(28) as usize, u16at(42), u16at(44));
        let mut mem = vec![0u8; MEM_SIZE];
        for i in 0..phnum {
            let o = phoff + i * phentsize;
            if u32at(o) != 1 {
                continue; // PT_LOAD only
            }
            let (off, vaddr, filesz, memsz) = (u32at(o + 4) as usize, u32at(o + 8) as usize, u32at(o + 16) as usize, u32at(o + 20) as usize);
            if vaddr + memsz > MEM_SIZE {
                return Err(format!("segment outside RAM: {vaddr:#x}+{memsz:#x}"));
            }
            mem[vaddr..vaddr + filesz].copy_from_slice(&elf[off..off + filesz]);
        }
        Ok(Emu { mem, regs: [0; 32], pc: entry, instret: 0 })
    }

    pub fn write_mem(&mut self, addr: u32, data: &[u8]) {
        self.mem[addr as usize..addr as usize + data.len()].copy_from_slice(data);
    }

    pub fn read_u32(&self, addr: u32) -> u32 {
        let a = addr as usize;
        u32::from_le_bytes([self.mem[a], self.mem[a + 1], self.mem[a + 2], self.mem[a + 3]])
    }

    fn ld(&self, a: u32, n: usize) -> Result<u32, String> {
        let a = a as usize;
        if a + n > MEM_SIZE {
            return Err(format!("load out of bounds at {a:#x}"));
        }
        let mut v = 0u32;
        for i in 0..n {
            v |= (self.mem[a + i] as u32) << (8 * i);
        }
        Ok(v)
    }

    fn st(&mut self, a: u32, n: usize, v: u32) -> Result<(), String> {
        let a = a as usize;
        if a + n > MEM_SIZE {
            return Err(format!("store out of bounds at {a:#x}"));
        }
        for i in 0..n {
            self.mem[a + i] = (v >> (8 * i)) as u8;
        }
        Ok(())
    }

    /// Run until `ecall` with a7 = 93 (exit). Returns the exit code.
    pub fn run(&mut self, max_instr: u64) -> Result<u32, String> {
        loop {
            if self.instret >= max_instr {
                return Err("instruction budget exceeded".into());
            }
            let pc = self.pc;
            let ins = self.ld(pc, 4).map_err(|e| format!("fetch: {e}"))?;
            let rd = ((ins >> 7) & 31) as usize;
            let rs1 = ((ins >> 15) & 31) as usize;
            let rs2 = ((ins >> 20) & 31) as usize;
            let f3 = (ins >> 12) & 7;
            let f7 = ins >> 25;
            let (a, b) = (self.regs[rs1], self.regs[rs2]);
            let imm_i = sx(ins >> 20, 12);
            let mut next = pc.wrapping_add(4);
            let mut wr: Option<u32> = None;
            match ins & 0x7F {
                0x37 => wr = Some(ins & 0xFFFF_F000),
                0x17 => wr = Some(pc.wrapping_add(ins & 0xFFFF_F000)),
                0x6F => {
                    let imm = sx(((ins >> 31) << 20) | (((ins >> 12) & 0xFF) << 12) | (((ins >> 20) & 1) << 11) | (((ins >> 21) & 0x3FF) << 1), 21);
                    wr = Some(next);
                    next = pc.wrapping_add(imm);
                }
                0x67 => {
                    wr = Some(next);
                    next = a.wrapping_add(imm_i) & !1;
                }
                0x63 => {
                    let imm = sx(((ins >> 31) << 12) | (((ins >> 7) & 1) << 11) | (((ins >> 25) & 0x3F) << 5) | (((ins >> 8) & 0xF) << 1), 13);
                    let t = match f3 {
                        0 => a == b,
                        1 => a != b,
                        4 => (a as i32) < (b as i32),
                        5 => (a as i32) >= (b as i32),
                        6 => a < b,
                        7 => a >= b,
                        _ => return Err(format!("bad branch f3 at {pc:#x}")),
                    };
                    if t {
                        next = pc.wrapping_add(imm);
                    }
                }
                0x03 => {
                    let ad = a.wrapping_add(imm_i);
                    wr = Some(match f3 {
                        0 => sx(self.ld(ad, 1)?, 8),
                        1 => sx(self.ld(ad, 2)?, 16),
                        2 => self.ld(ad, 4)?,
                        4 => self.ld(ad, 1)?,
                        5 => self.ld(ad, 2)?,
                        _ => return Err(format!("bad load f3 at {pc:#x}")),
                    });
                }
                0x23 => {
                    let imm = sx(((ins >> 25) << 5) | ((ins >> 7) & 31), 12);
                    let ad = a.wrapping_add(imm);
                    match f3 {
                        0 => self.st(ad, 1, b)?,
                        1 => self.st(ad, 2, b)?,
                        2 => self.st(ad, 4, b)?,
                        _ => return Err(format!("bad store f3 at {pc:#x}")),
                    }
                }
                0x13 => {
                    let sh = (ins >> 20) & 31;
                    wr = Some(match f3 {
                        0 => a.wrapping_add(imm_i),
                        2 => ((a as i32) < (imm_i as i32)) as u32,
                        3 => (a < imm_i) as u32,
                        4 => a ^ imm_i,
                        6 => a | imm_i,
                        7 => a & imm_i,
                        1 => a << sh,
                        5 => {
                            if f7 & 0x20 != 0 {
                                ((a as i32) >> sh) as u32
                            } else {
                                a >> sh
                            }
                        }
                        _ => unreachable!(),
                    });
                }
                0x33 => {
                    wr = Some(if f7 == 1 {
                        match f3 {
                            0 => a.wrapping_mul(b),
                            1 => (((a as i32 as i64) * (b as i32 as i64)) >> 32) as u32,
                            2 => (((a as i32 as i64) * (b as u64 as i64)) >> 32) as u32,
                            3 => (((a as u64) * (b as u64)) >> 32) as u32,
                            4 => {
                                if b == 0 {
                                    u32::MAX
                                } else if a as i32 == i32::MIN && b as i32 == -1 {
                                    a
                                } else {
                                    ((a as i32) / (b as i32)) as u32
                                }
                            }
                            5 => {
                                if b == 0 {
                                    u32::MAX
                                } else {
                                    a / b
                                }
                            }
                            6 => {
                                if b == 0 {
                                    a
                                } else if a as i32 == i32::MIN && b as i32 == -1 {
                                    0
                                } else {
                                    ((a as i32) % (b as i32)) as u32
                                }
                            }
                            _ => {
                                if b == 0 {
                                    a
                                } else {
                                    a % b
                                }
                            }
                        }
                    } else {
                        match f3 {
                            0 => {
                                if f7 & 0x20 != 0 {
                                    a.wrapping_sub(b)
                                } else {
                                    a.wrapping_add(b)
                                }
                            }
                            1 => a << (b & 31),
                            2 => ((a as i32) < (b as i32)) as u32,
                            3 => (a < b) as u32,
                            4 => a ^ b,
                            5 => {
                                if f7 & 0x20 != 0 {
                                    ((a as i32) >> (b & 31)) as u32
                                } else {
                                    a >> (b & 31)
                                }
                            }
                            6 => a | b,
                            _ => a & b,
                        }
                    });
                }
                0x0F => {}
                0x73 => {
                    if f3 == 0 {
                        if ins >> 20 == 0 {
                            if self.regs[17] == 93 {
                                self.instret += 1;
                                return Ok(self.regs[10]);
                            }
                            return Err(format!("unsupported ecall a7={} at {pc:#x}", self.regs[17]));
                        }
                        return Err(format!("ebreak at {pc:#x}"));
                    }
                    let csr = ins >> 20;
                    wr = Some(match csr {
                        0xC00 | 0xB00 | 0xC01 | 0xC02 | 0xB02 => self.instret as u32,
                        0xC80 | 0xB80 | 0xC81 | 0xC82 | 0xB82 => (self.instret >> 32) as u32,
                        _ => return Err(format!("unsupported csr {csr:#x} at {pc:#x}")),
                    });
                }
                op => return Err(format!("illegal opcode {op:#x} (ins {ins:#010x}) at {pc:#x}")),
            }
            if let Some(v) = wr {
                if rd != 0 {
                    self.regs[rd] = v;
                }
            }
            self.pc = next;
            self.instret += 1;
        }
    }
}
