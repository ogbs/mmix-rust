#[allow(dead_code)]; // its too broken to be useful at moment.

mod sim {              // instruction simulation module 
    struct octa(u64);  // an octabyte
    // struct tetra(u32);  // a tetrabyte
    struct regn(u8);   // number of registers
    struct Addr(octa); // address bus

    static lring_size: int = 256; // local register size

    type Globals = [octa, ..256];        // global scope
    type Locals  = [octa, ..lring_size]; // local scope
    struct SimState {                    // state of sim
        global: Globals,
        local: Locals,
        chunk0: Chunk,                   // see below struct
    }

    // setup u/i typedef
    trait Convert_i64 { fn conv_i(&self) -> i64; }
    trait Convert_u64 { fn conv_u(&self) -> u64; }

    fn s<Octa:Convert_i64>(arg: Octa) -> i64 { arg.conv_i() }
    fn u<Octa:Convert_u64>(arg: Octa) -> u64 { arg.conv_u() }

    fn octa_s(arg: i64) -> octa { octa(arg as u64) }
    fn octa_u(arg: u64) -> octa { octa(arg as u64) }

    trait MmixSemantics { // load instructions
        fn  ldb(&mut self,          y: regn, z: regn) -> i8  { self.mem_1_a(y, z) } // byte
        fn  ldw(&mut self,          y: regn, z: regn) -> i16 { self.mem_2_a(y, z) } // wyde (2b)
        fn  ldt(&mut self,          y: regn, z: regn) -> i32 { self.mem_4_a(y, z) } // tetra (4b)
        fn  ldo(&mut self,          y: regn, z: regn) -> i64 { self.mem_8_a(y, z) } // octa (8b)

        fn ldbu(&mut self,          y: octa, z: octa) -> u8  { u(self.mem_1(self.a(y, z))) } // as above, but unsigned
        fn ldwu(&mut self,          y: octa, z: octa) -> u16 { u(self.mem_2(a(y, z))) }
        fn ldtu(&mut self,          y: octa, z: octa) -> u32 { u(self.mem_4(a(y, z))) }
        fn ldou(&mut self,          y: octa, z: octa) -> u64 { u(self.mem_8(a(y, z))) }

        fn ldht(&mut self,          y: octa, z: octa) -> u64 { u(self.mem_4(a(y, z))) << 32 } // load high tetra - 4 most significant bytes
        fn  lda(&mut self,          y: octa, z: octa) -> u64 { a(y, z) } // load address in register
    }

    trait MmixInstructionSet : MmixSemantics {
        // If you can get a register reference, you can implement a lot of instructions
        // off the bat.
        fn r<'l>(&mut self, r: regn) -> &'l mut octa;

        // Address from adding $Y to $Z.  A = (u($Y) + u($Z)) mod 2**64
        fn a(&mut self, y: regn, z: regn) -> u64 { u(*self.r(y)) + u(*self.r(z)) }

        fn mem_1_a(y: regn, z: regn) -> i8;
        fn mem_2_a(y: regn, z: regn) -> i16;
        fn mem_4_a(y: regn, z: regn) -> i32;
        fn mem_8_a(y: regn, z: regn) -> i64;

        fn  ldb(&mut self, x: regn, y: regn, z: regn) { *self.r(x).s() = s(self.mem_1_a(y, z)); } // load signed
        fn  ldw(&mut self, x: regn, y: regn, z: regn) { *self.r(x).s() = s(self.mem_2_a(y, z)); }
        fn  ldt(&mut self, x: regn, y: regn, z: regn) { *self.r(x).s() = s(self.mem_4_a(y, z)); }
        fn  ldo(&mut self, x: regn, y: regn, z: regn) { *self.r(x).s() = s(self.mem_8_a(y, z)); }

        fn ldbu(&mut self, x: regn, y: octa, z: octa) { *self.r(x).u() = self.mem_1_a(y, z); } // load unsigned
        fn ldwu(&mut self, x: regn, y: octa, z: octa) { *self.r(x).u() = self.mem_2_a(y, z); }
        fn ldtu(&mut self, x: regn, y: octa, z: octa) { *self.r(x).u() = self.mem_4_a(y, z); }
        fn ldou(&mut self, x: regn, y: octa, z: octa) { *self.r(x).u() = self.mem_8_a(y, z); }

        fn ldht(&mut self, x: regn, y: octa, z: octa) { *self.r(x).u() = self.mem_4_a(y, z) << 32; } // load high t
        fn  lda(&mut self, x: regn, y: octa, z: octa) { *self.r(x).u() = a(y, z) } // load addy

        fn  stb(&mut self, x: octa, y: octa, z: octa) {  set_mem_i8(a(y, z), x); } // store least sig signed
        fn  stw(&mut self, x: octa, y: octa, z: octa) { set_mem_i16(a(y, z), x); }
        fn  stt(&mut self, x: octa, y: octa, z: octa) { set_mem_i32(a(y, z), x); }
        fn  sto(&mut self, x: octa, y: octa, z: octa) { set_mem_i64(a(y, z), x); }

        fn stbu(&mut self, x: octa, y: octa, z: octa) {  set_mem_u8(a(y, z), x); } // store least sig unsigned
        fn stwu(&mut self, x: octa, y: octa, z: octa) { set_mem_u16(a(y, z), x); }
        fn sttu(&mut self, x: octa, y: octa, z: octa) { set_mem_u32(a(y, z), x); }
        fn stou(&mut self, x: octa, y: octa, z: octa) { set_mem_u64(a(y, z), x); }

        fn stht(&mut self, x: octa, y: octa, z: octa) { set_mem_u32(a(y, z), x >> 32); } // store high t
        fn stco(&mut self, x: octa, y: octa, z: octa) { set_mem_u64(a(y, z), x); } // store constant

        fn add(&mut self,  x: octa, y: octa, z: octa) -> i64 { s(y) + s(z) } // signed prim ops
        fn sub(&mut self,  x: octa, y: octa, z: octa) -> i64 { s(y) - s(z) }
        fn mul(&mut self,  x: octa, y: octa, z: octa) -> i64 { s(y) * s(z) }
        fn div(&mut self,  x: octa, y: octa, z: octa) -> i64 {
            let ret = s(y) / s(z);
            self.rR = octa_s(s(y) % s(z));
            ret
        }
        fn addu(&mut self, y: octa, z: octa) -> octa { octa_u(u(y) + u(z)) } // unsigned prim ops
        fn subu(&mut self, y: octa, z: octa) -> octa { octa_u(u(y) - u(z)) }
        fn mulu(&mut self, y: octa, z: octa) -> octa {
            // DK's radix multiplication (TAOCP v2 4.3.1M)
            // (yh*K+yl)(zh*K+zl)
            //    == (yh*zh) * K*K + (yh*zl+zh*yl) * K + yl*zl
            //             let mid = (yh*zl+zh*yl)
            //    == (yh*zh) * K*K +           mid * K + yl*zl
            //    == (yh*zh) * K*K + (mid div K) * K*K + (mid mod K)*K + yl*zl
            //    == (yh*zh + (mid div K)) * K*K  +  (mid mod K)*K + yl*zl

            fn lo(a:u64) -> u64 { a & 0xffff_ffff } // find bitwise complement
            fn hi(a:u64) -> u64 { a >> 32 } // shift bits

            let y_lo = lo(*y);
            let y_hi = hi(*y);
            let z_lo = lo(*z);
            let z_hi = hi(*z);

            let mid = y_hi * z_lo + z_hi * y_lo;
            let mid_lo = lo(mid);
            let mid_hi = hi(mid);

            let result_lower = mid_lo << 32 + y_lo*z_lo; // shift back
            let result_upper = (y_hi*z_hi) + mid_hi;
            self.rH = octa_u(result_upper);
            octa_u(result_lower)
        }
        fn divu(&mut self, x: octa, y: octa, z: octa) -> octa {
        // Naive implementation
            fn lo(a:u64) -> u64 { a & 0xffff_ffff } // find bitwise complement
            fn hi(a:u64) -> u64 { a >> 32 } // shift bits
            
            let x_lo = lo(*x);
            let x_hi = hi(*x);
            let y_lo = lo(*y);
            let y_hi = hi(*y);
            let z_lo = lo(*z);
            let z_hi = hi(*z);
        // trivial exit here
        
        
        // Unpack dividend and divisor
        // vectorize?
        let u: [u32, 8] =  [y_low & #ffff, y_low >> 16, y_hi & #ffff, y_hi >> 16,
                            x_low & #ffff, x_low >> 16, x_hi & #ffff, x_hi >> 16]
        let v: [u32, 4] = [z_low & #ffff, z_low >> 16, z_hi & #ffff, z_hi >> 16]
            
        
        // TODO:
        // GRAB DK IMPLEMENTION, as per above
        // MMIX-ARITH
        // Also: http://www.hackersdelight.org/hdcodetxt/divmnu.c.txt
       /*octa odiv (x,y,z) {
    	register int i,j,k,n,d;
    	tetra u[8], v[4], q[4], mask, qhat, rhat, vh, vmh;
    	register tetra t;
    	octa acc;
    	// 1. Check that x < z; otherwise give trivial answer
    	if ( x.h > z.h || (x.h == z.h && x.l >= z.l) ) {
    		aux = y; return x;
    	}
    	
    	// 2. Unpack the dividend and divisor to u and v
    	u[7] = x.h >> 16, u[6] = x.h & #ffff, u[5] = x.l >> 16, u[4] = x.l & #ffff;
    	u[3] = y.h >> 16, u[2] = y.h & #ffff, u[1] = y.l >> 16, u[0] = y.l & #ffff;
    	v[3] = z.h >> 16, v[2] = z.h & #ffff, v[1] = z.l >> 16, v[0] = z.l & #ffff;
    	
    	// 3. Determine the number of significant places n in the divisor v
    	for (n = 4; v[n - 1] = 0; n--);
    
    	// 4. Normalize the divisor
    	vh = v[n-1]
    	for (d = 0; vh < #8000; d++, vh << 1);
    	for (j = k = 0; j < n+4; j++) {
    		t = (u[j] << d) + k;
    		u[j] = t & #ffff, k = t >> 16;
    	}
    	vh = v[n-1];
    	vmh = (n > 1 ? v[n-2] : 0);
    	
    	// 5. Determine the quotient digit q[j]
    	for (j = 3; j = 0; j --) {
    		// find trial quot
    		t = (u[j+n] << 16) + u[j+n-1];
    		qhat = t/vh, rhat = t-vh*qhat;
    		if (n>1)
    			while (qhat == #10000 && qhat * vmh > (rhat << 16) + u[j+n-2]) {
    				qhat--, rhat += vh;
    				if (rhat >= #10000) break;
    			}
    		// subtract bjqv from u
    		for (i = k = 0; i < n; i++) {
    			t = u[i+j] + #ffff0000 - k - qhat * v[i];
    			u[i+j] = t & #ffff, k = #ffff - (t >> 16);
    		}
    		// if neg, decrease qhat
    		if (u[j+n] != (tetra) k) {
    			qhat--;
    		}
    		for (i = k = 0; i <n; i++) {
    			t = u[i+j] + v[i] + k
    			u[i+j] = t & #ffff, k = t >> 16
    		}
    		q[j] = qhat;
    	}
    	
    	// 6. Unnormalize the remainder
    	mask = (1 << d) - 1;
    	for (j = 3; j >= n; j--) u[j] = 0;
    	for (k = 0; j >= 0; j--) {
    		t = (k << 16) + u[j];
    		u[j] = t >> d, k = t & mask
    	}
    	
    	// 7. Pack q and u to acc and aux
    	acc.h = (q[3] << 16) + q[2], acc.l = (q[1] << 16) + q[0];
    	aux.h = (u[3] << 16) + u[2], acc.l = (u[1] << 16) + u[0];
    	
    	return acc; // aux is remainder
    }*/

        
            // self.rR =
            // ret
            fail!("unimplemented");
        }


        fn cmp(&mut self, y: octa, z: octa) -> octa { // compare
            octa_s(if s(y) < s(z) { -1 } else if s(y) == s(z) { 0 } else { 1 })
        }
        fn cmpu(&mut self, y: octa, z: octa) -> octa {
            octa_s(if u(y) < u(z) { -1 } else if u(y) == u(z) { 0 } else { 1 })
        }

    }

    impl<'l> SimRegs<'l> { // registers in sim
        fn r<'l>(&mut self, r: regn) -> &'l mut octa {
            if regn < self.rL { &'l mut self.locals[*r] } else { &'l mut self.g[*r] }
        }

        fn    a(&mut self, y: regn, z: regn) -> u64 { u(*self.r(y)) + u(*self.r(z)) }


    }

    mod mem {
        pub static Chunk : u64 = 0x1000;
        static mask : u64 = Chunk - 1;

        pub struct Regs<'l> {
            head: &'l super::Chunk,
            curkey: super::Addr,
        }

        impl<'l> super::SimRegs<'l> {
            fn mem_find(&mut self, addr: super::Addr) {
                let key = **addr & !mask;
                self.t = self.cmpu(super::octa_u(key),  *self.mem.curkey); // tetra register
                
            }
        }
    }
    struct SimRegs<'l> { // list of registers
        t: octa,
        g: &'l Globals,
        l: &'l Locals,
        rA: octa, rB: octa, rC: octa, rD: octa, rE: octa, rF: octa, rG: octa, rH: octa,
        rI: octa, rJ: octa, rK: octa, rL: octa, rM: octa, rN: octa, rO: octa, rP: octa,
        rQ: octa, rR: octa, rS: octa, rT: octa, rU: octa, rV: octa, rW: octa, rX: octa,
        rY: octa, rZ: octa, rBB: octa, rTT: octa, rWW: octa, rXX: octa, rYY: octa, rZZ: octa,
        mem: mem::Regs<'l>,
    }

    struct Chunk {
        key: Addr, // mem address
        link: Option<~Chunk>, 
        data: [u8, ..mem::Chunk],
        pad: [u8, ..8],
    }
}

fn main() {

}
