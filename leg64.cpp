// Copyright (C) 2019, David S. Hardin
// License: A 3-clause BSD license.  See the LICENSE file in this directory.

// ------------------------------------------------------------------------
// LEG64 Simulator


#include "leg64.h"


// Initialization

leg64St zeroRegs(leg64St s) {
  for (uint i = REG_SZ; i > 0; i--) {
    s.regs[i-1] = 0;
  }
  return s;
}


leg64St zeroDmem(leg64St s) {
  for (uint i = DMEM_SZ; i > 0; i--) {
    s.dmem[i-1] = 0;
  }
  return s;
}


leg64St zeroCmem(leg64St s) {
  for (uint i = CMEM_SZ; i > 0; i--) {
    s.cmem[i-1] = 0;
  }
  return s;
}


leg64St resetAll(leg64St s) {
  //  s.err = 0;
  s.pc = 0;
  s.sp = 0;
  // s.insCount = 0;

  s.opcode = NOP;
  s.op1 = 0;
  s.op2 = 0;
  s.op3 = 0;

  s.C = 0;
  s.N = 0;
  s.Z = 0;
  s.V = 0;
  
  s = zeroRegs(s);
  s = zeroDmem(s);
  s = zeroCmem(s);
  
  return s;
}


leg64St resetAllButCmem(leg64St s) {
  //  s.err = 0;
  s.pc = 0;
  s.sp = 0;
  //  s.insCount = 0;

  s.opcode = NOP;
  s.op1 = 0;
  s.op2 = 0;
  s.op3 = 0;

  s.C = 0;
  s.N = 0;
  s.Z = 0;
  s.V = 0;
  
  s = zeroRegs(s);
  s = zeroDmem(s);

  return s;
}


leg64St nextInst(leg64St s) {
  ui32 codewd = s.cmem[s.pc];
    
  s.opcode = codewd.slc<8>(24);
  s.op1 = codewd.slc<8>(16);
  s.op2 = codewd.slc<8>(8);
  s.op3 = codewd.slc<8>(0);
  s.pc = s.pc + 1;
    //    s.insCount++;
  return s;
}


// We define the semantics of each instruction.  Most of these functions 
// are slight abstractions of actual LLVM instructions, and have the 
// standard LLVM three-address form.  I have also held over a few M1 
// stack-based instructions to be used in register initialization,
// phi processing, etc.


// Memory Instructions


// (LDR j k): Assign the reg j the value at the memory address stored
// in reg k.

leg64St do_LDR(leg64St s) {
 ui12 addr = s.regs[s.op2] & 0xfff;

 s.regs[s.op1] = s.dmem[addr];
 return s;
}

// (STR j k): Store the value stored in reg k at the
// memory address stored in reg j.

leg64St do_STR(leg64St s) {
 ui12 addr = s.regs[s.op1] & 0xfff;

 s.dmem[addr] = s.regs[s.op2];
  return s;
}

// Arithmetic/Logic Instructions

// (ADD a b c): Set the value of the first reg to the sum of the
// second and third regs.

leg64St do_ADD(leg64St s) {
  s.regs[s.op1] = s.regs[s.op2] + s.regs[s.op3];
  return s;
}

// (ADDI a b c): Set the value of the first reg to the sum of the
// second reg and the (small) literal c

leg64St do_ADDI(leg64St s) {
  s.regs[s.op1] = s.regs[s.op2] + s.op3;
  return s;
}

// (CMP a b): Compare regs a and b
// Set the condition codes as follows:
//  Set Z if a = b
//  Set N if a - b is negative
//  Set C is a - b is positive

leg64St do_CMP(leg64St s) {
  ui64 res = s.regs[s.op1] - s.regs[s.op2];

  if (res == 0) {
    s.C = 0;
    s.N = 0;
    s.V = 0;
    s.Z = 1;
  } else if ((res & 0x8000000000000000) == 0x8000000000000000) {  // negative
    s.C = 0;
    s.N = 1;
    s.V = 0;
    s.Z = 0;
  } else { // positive
    s.C = 1;
    s.N = 0;
    s.V = 0;
    s.Z = 0;
  }
  return s;
}
      
// (CMPI a b): Compare reg a and (small) literal value b
// Set the condition codes as follows:
//  Set Z if a = b
//  Set N if a - b is negative
//  Set C is a - b is positive

leg64St do_CMPI(leg64St s) {
  ui64 res = s.regs[s.op1] - s.op2;

  if (res == 0) {
    s.C = 0;
    s.N = 0;
    s.V = 0;
    s.Z = 1;
  } else if ((res & 0x8000000000000000) == 0x8000000000000000) {  // negative
    s.C = 0;
    s.N = 1;
    s.V = 0;
    s.Z = 0;
  } else { // positive
    s.C = 1;
    s.N = 0;
    s.V = 0;
    s.Z = 0;
  }
  return s;
}


// (CONST a b c): Set the value of the first reg 
// to the constant formed by ((b << 8) | c).

leg64St do_CONST(leg64St s) {
  ui64 k = (((ui64)s.op2 << 8) | s.op3);
  s.regs[s.op1] = k;
  return s;
}


// (MUL a b c): Set the value of the first reg 
// to the product of the second and third regs.

leg64St do_MUL(leg64St s) {
  s.regs[s.op1] = s.regs[s.op2] * s.regs[s.op3];
  return s;
}

// (SUB a b c): Set the value of the first reg
// to the difference of the second and third regs.

leg64St do_SUB(leg64St s) {
  s.regs[s.op1] = s.regs[s.op2] - s.regs[s.op3];
  return s;
}

// (SUBI a b c): Set the value of reg a to the difference of 
// reg b and (small) literal c.

leg64St do_SUBI(leg64St s) {
  s.regs[s.op1] = s.regs[s.op2] - s.op3;
  return s;
}


// Transfer of Control Instructions

// (B i): adjust the pc by i

leg64St do_B(leg64St s) {
  if (s.op1 > 127) {
    s.pc = s.pc + (s.op1 - 256);
  } else {
    s.pc = s.pc + s.op1;
  }
  return s;
}

// (BEQ k): Adjust the pc by k if Z == 1

leg64St do_BEQ(leg64St s) {
  if (s.Z == 1) {
    if (s.op1 > 127) {
      s.pc = s.pc + (s.op1 - 256);
    } else {
      s.pc = s.pc + s.op1;
    }
  }
  return s;
}

// (BNE k): Adjust the pc by k if Z == 0

leg64St do_BNE(leg64St s) {
  if (s.Z == 0) {
    if (s.op1 > 127) {
      s.pc = s.pc + (s.op1 - 256);
    } else {
      s.pc = s.pc + s.op1;
    }
  }
  return s;
}

// (BLS k): Adjust the pc by k if unsigned lower or same
// (C == 0 || Z == 1)

leg64St do_BLS(leg64St s) {
  if (s.C == 0 || s.Z == 1) {
    if (s.op1 > 127) {
      s.pc = s.pc + (s.op1 - 256);
    } else {
      s.pc = s.pc + s.op1;
    }
  }
  return s;
}

// (BHI k): Adjust the pc by k if unsigned higher
// (C == 1)

leg64St do_BHI(leg64St s) {
  if (s.C == 1) {
    if (s.op1 > 127) {
      s.pc = s.pc + (s.op1 - 256);
    } else {
      s.pc = s.pc + s.op1;
    }
  }
  return s;
}


// (HALT): chase tail

leg64St do_HALT(leg64St s) {
  s.pc = s.pc - 1;
  //    s.insCount--;
  return s;
}


// (NOP): No operation

leg64St do_NOP(leg64St s) {
  return s;
}


// Instruction selector

leg64St do_Inst(leg64St s) {
  ui8 opc = s.opcode;
  
  if (opc == ADD) {
     return do_ADD(s);
  } else if (opc == ADDI) {
    return do_ADDI(s);
  } else if (opc == B) {
    return do_B(s);
  } else if (opc == BEQ) {
    return do_BEQ(s);
  } else if (opc == BHI) {
    return do_BHI(s);
  } else if (opc == BLS) {
    return do_BLS(s);
  } else if (opc == BNE) {
    return do_BNE(s);
  } else if (opc == CMP) {
    return do_CMP(s);
  } else if (opc == CMPI) {
    return do_CMPI(s);
  } else if (opc == CONST) {
    return do_CONST(s);
  } else if (opc == MUL) {
    return do_MUL(s);
  } else if (opc == NOP) {
    return do_NOP(s);
  } else if (opc == SUB) {
   return do_SUB(s);
  } else if (opc == SUBI) {
    return do_SUBI(s);
  } else if (opc == HALT) {
    return do_HALT(s);
  } else if (opc == LDR) {
    return do_LDR(s);
  } else if (opc == STR) {
    return do_STR(s);
  } else {
    return do_HALT(s);
    //   s.pc = s.pc - 1;
    //    s.err = 3;
    return s;
  }
}


leg64St leg64step(leg64St s) {
  return do_Inst(nextInst(s));
}

leg64St leg64steps(leg64St s, uint count) {
  for (uint i = count;
       (i > 0); // && (s.err == 0));
       i--) {
    s = leg64step(s);
  }
  return s;
}

// Produce by online GCC compiler at -O3 optimization

leg64St doFactO3(ui8 n, leg64St s) {

  //  s = resetAll(s);

  // The algorithm of *fact-program* is as follows.  reg[0] holds the input.

  s.regs[0] = n;

  s.regs[1] = 1;  // accum

  ui10 k = 0;    // Beginning code address
  
  //  '((CONST 0 0 n)     ; 0   r0 <- n
  s.cmem[k] = ((CONST & 0xff) << 24) | (n & 0xff); k=k+1;

  //    (CONST 1 0 1)     ; 1   r1 <- 1
  s.cmem[k] = ((CONST & 0xff) << 24) | (1 << 16) | 1; k=k+1;

  //    (CMPI 0 1)        ; 2
  s.cmem[k] = ((CMPI & 0xff) << 24) | (1 << 8) | 0; k=k+1;

  //      (BLS .L2)       ; 3
  s.cmem[k] = ((BLS & 0xff) << 24) | (4 << 16) | 0; k=k+1;

  // .L3  (MUL 1 1 0)     ; 4   r1 = r1 * r0 <-- loop
  s.cmem[k] = ((MUL & 0xff) << 24) | (1 << 16) | (1 << 8) | 0; k=k+1;

  //      (SUBI 0 0 1)    ; 5   r0 = r0 - 1
  s.cmem[k] = ((SUBI & 0xff) << 24) | 1; k=k+1;

  //      (CMPI 0 1)      ; 6
  s.cmem[k] = ((CMPI & 0xff) << 24) | (1 << 8) | 0; k=k+1;

  //      (BNE .L3)       ; 7
  s.cmem[k] = ((BNE & 0xff) << 24) | (0xfc << 16) | 0; k=k+1;

  // .L2  (ADDI 0 1 0)    ; 8   r0 <- r1
  s.cmem[k] = ((ADDI & 0xff) << 24) | (1 << 8) | 0; k=k+1;

  //      (HALT)))        ; 9   halt with factorial result in reg[1]
  s.cmem[k] = ((HALT & 0xff) << 24) | 0;

  s = leg64steps(s, ((4 + ((uint)n * 4)) + 2));

  return s;
}


leg64St doFact(ui8 n, leg64St s) {

  //  s = resetAll(s);

  // The algorithm of *fact-program* is as follows.  reg[0] holds the input.

  s.regs[0] = n;

  s.regs[1] = 1;      // accum

  ui10 k = 0;    // Beginning code address
  
  //    '((CONST 0 0 n)   ; 0   r0 <- n
  s.cmem[k] = ((CONST & 0xff) << 24) | (n & 0xff); k=k+1;

  //      (CONST 1 0 1)   ; 1   r1 <- 1
  s.cmem[k] = ((CONST & 0xff) << 24) | (1 << 16) | 1; k=k+1;

  //      (CONST 2 0 20)  ; 2   r2 <- 20
  s.cmem[k] = ((CONST & 0xff) << 24) | (2 << 16) | 20; k=k+1;

  //      (CMP 0 2))      ; 3
  s.cmem[k] = ((CMP & 0xff) << 24) | (2 << 8) | 0; k=k+1;

  //      (BHI .L2)       ; 4
  s.cmem[k] = ((BHI & 0xff) << 24) | (5 << 16) | 0; k=k+1;

  //      (CMPI 0 0)      ; 5
  s.cmem[k] = ((CMPI & 0xff) << 24) | 0; k=k+1;

  //      (BEQ .L2)       ; 6
  s.cmem[k] = ((BEQ & 0xff) << 24) | (3 << 16) | 0; k=k+1;

  // .L3  (MUL 1 1 0)     ; 7   r1 = r1 * r0 <-- loop
  s.cmem[k] = ((MUL & 0xff) << 24) | (1 << 16) | (1 << 8) | 0; k=k+1;

  //      (SUBI 0 0 1)    ; 8   r0 = r0 - 1
  s.cmem[k] = ((SUBI & 0xff) << 24) | 1; k=k+1;

  //      (B .L3)         ; 9
  s.cmem[k] = ((B & 0xff) << 24) | (0xfb << 16) | 0; k=k+1;

  // .L2  (ADDI 0 1 0)    ; 10  r0 <- r1
  s.cmem[k] = ((ADDI & 0xfb) << 24) | (1 << 8) | 0; k=k+1;

  //      (HALT)))        ; 11  halt with factorial result in reg[1]
  s.cmem[k] = ((HALT & 0xff) << 24) | 0;

  s = leg64steps(s, (5 + ((uint)n * 5) + 3));

  return s;
}


#ifdef COMPILE_ME

int main (int argc, char *argv[]) {

  cout << "Reset" << endl;

  leg64St s;

  s = resetAll(s);
  s.pc = 0;

  s = doFactO3(20, s);

  cout << "r0 = " << s.regs[0] << endl;
  cout << "r1 = " << s.regs[1] << endl;
  cout << "pc = " << s.pc << endl;
  //  cout << "err = " << s.err << endl;
  //  cout << "insCount = " << s.insCount << endl;

  s = resetAll(s);
  s.pc = 0;

  s = doFact(20, s);

  cout << "r0 = " << s.regs[0] << endl;
  cout << "r1 = " << s.regs[1] << endl;
  cout << "pc = " << s.pc << endl;
  //  cout << "err = " << s.err << endl;
  //  cout << "insCount = " << s.insCount << endl;
  
  return 0;
}

#endif
