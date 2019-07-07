(IN-PACKAGE "RTL")

(INCLUDE-BOOK "rtl/rel11/lib/rac" :DIR :SYSTEM)

(SET-IGNORE-OK T)

(SET-IRRELEVANT-FORMALS-OK T)

(DEFUN ZEROREGS-LOOP-0 (I S)
       (DECLARE (XARGS :MEASURE (NFIX (- I 0))))
       (IF (AND (INTEGERP I) (> I 0))
           (LET ((S (AS 'REGS
                        (AS (- I 1) (BITS 0 63 0) (AG 'REGS S))
                        S)))
                (ZEROREGS-LOOP-0 (- I 1) S))
           S))

(DEFUN ZEROREGS (S)
       (ZEROREGS-LOOP-0 256 S))

(DEFUN ZERODMEM-LOOP-0 (I S)
       (DECLARE (XARGS :MEASURE (NFIX (- I 0))))
       (IF (AND (INTEGERP I) (> I 0))
           (LET ((S (AS 'DMEM
                        (AS (- I 1) (BITS 0 63 0) (AG 'DMEM S))
                        S)))
                (ZERODMEM-LOOP-0 (- I 1) S))
           S))

(DEFUN ZERODMEM (S)
       (ZERODMEM-LOOP-0 4096 S))

(DEFUN ZEROCMEM-LOOP-0 (I S)
       (DECLARE (XARGS :MEASURE (NFIX (- I 0))))
       (IF (AND (INTEGERP I) (> I 0))
           (LET ((S (AS 'CMEM
                        (AS (- I 1) (BITS 0 31 0) (AG 'CMEM S))
                        S)))
                (ZEROCMEM-LOOP-0 (- I 1) S))
           S))

(DEFUN ZEROCMEM (S)
       (ZEROCMEM-LOOP-0 1024 S))

(DEFUN RESETALL (S)
       (LET* ((S (AS 'PC (BITS 0 9 0) S))
              (S (AS 'SP (BITS 0 11 0) S))
              (S (AS 'OPCODE (BITS 12 7 0) S))
              (S (AS 'OP1 (BITS 0 7 0) S))
              (S (AS 'OP2 (BITS 0 7 0) S))
              (S (AS 'OP3 (BITS 0 7 0) S))
              (S (AS 'C (BITS 0 0 0) S))
              (S (AS 'N (BITS 0 0 0) S))
              (S (AS 'Z (BITS 0 0 0) S))
              (S (AS 'V (BITS 0 0 0) S))
              (S (ZEROREGS S))
              (S (ZERODMEM S)))
             (ZEROCMEM S)))

(DEFUN RESETALLBUTCMEM (S)
       (LET* ((S (AS 'PC (BITS 0 9 0) S))
              (S (AS 'SP (BITS 0 11 0) S))
              (S (AS 'OPCODE (BITS 12 7 0) S))
              (S (AS 'OP1 (BITS 0 7 0) S))
              (S (AS 'OP2 (BITS 0 7 0) S))
              (S (AS 'OP3 (BITS 0 7 0) S))
              (S (AS 'C (BITS 0 0 0) S))
              (S (AS 'N (BITS 0 0 0) S))
              (S (AS 'Z (BITS 0 0 0) S))
              (S (AS 'V (BITS 0 0 0) S))
              (S (ZEROREGS S)))
             (ZERODMEM S)))

(DEFUN NEXTINST (S)
       (LET* ((CODEWD (AG (AG 'PC S) (AG 'CMEM S)))
              (S (AS 'OPCODE (BITS CODEWD 31 24) S))
              (S (AS 'OP1 (BITS CODEWD 23 16) S))
              (S (AS 'OP2 (BITS CODEWD 15 8) S))
              (S (AS 'OP3 (BITS CODEWD 7 0) S)))
             (AS 'PC (BITS (+ (AG 'PC S) 1) 9 0) S)))

(DEFUN DO_LDR (S)
       (LET ((ADDR (BITS (LOGAND (AG (AG 'OP2 S) (AG 'REGS S))
                                 4095)
                         11 0)))
            (AS 'REGS
                (AS (AG 'OP1 S)
                    (AG ADDR (AG 'DMEM S))
                    (AG 'REGS S))
                S)))

(DEFUN DO_STR (S)
       (LET ((ADDR (BITS (LOGAND (AG (AG 'OP1 S) (AG 'REGS S))
                                 4095)
                         11 0)))
            (AS 'DMEM
                (AS ADDR (AG (AG 'OP2 S) (AG 'REGS S))
                    (AG 'DMEM S))
                S)))

(DEFUN DO_ADD (S)
       (AS 'REGS
           (AS (AG 'OP1 S)
               (BITS (+ (AG (AG 'OP2 S) (AG 'REGS S))
                        (AG (AG 'OP3 S) (AG 'REGS S)))
                     63 0)
               (AG 'REGS S))
           S))

(DEFUN DO_ADDI (S)
       (AS 'REGS
           (AS (AG 'OP1 S)
               (BITS (+ (AG (AG 'OP2 S) (AG 'REGS S))
                        (AG 'OP3 S))
                     63 0)
               (AG 'REGS S))
           S))

(DEFUN DO_CMP (S)
       (LET ((RES (BITS (- (AG (AG 'OP1 S) (AG 'REGS S))
                           (AG (AG 'OP2 S) (AG 'REGS S)))
                        63 0)))
            (IF1 (LOG= RES 0)
                 (LET* ((S (AS 'C (BITS 0 0 0) S))
                        (S (AS 'N (BITS 0 0 0) S))
                        (S (AS 'V (BITS 0 0 0) S)))
                       (AS 'Z (BITS 1 0 0) S))
                 (IF1 (LOG= (LOGAND RES 9223372036854775808)
                            9223372036854775808)
                      (LET* ((S (AS 'C (BITS 0 0 0) S))
                             (S (AS 'N (BITS 1 0 0) S))
                             (S (AS 'V (BITS 0 0 0) S)))
                            (AS 'Z (BITS 0 0 0) S))
                      (LET* ((S (AS 'C (BITS 1 0 0) S))
                             (S (AS 'N (BITS 0 0 0) S))
                             (S (AS 'V (BITS 0 0 0) S)))
                            (AS 'Z (BITS 0 0 0) S))))))

(DEFUN DO_CMPI (S)
       (LET ((RES (BITS (- (AG (AG 'OP1 S) (AG 'REGS S))
                           (AG 'OP2 S))
                        63 0)))
            (IF1 (LOG= RES 0)
                 (LET* ((S (AS 'C (BITS 0 0 0) S))
                        (S (AS 'N (BITS 0 0 0) S))
                        (S (AS 'V (BITS 0 0 0) S)))
                       (AS 'Z (BITS 1 0 0) S))
                 (IF1 (LOG= (LOGAND RES 9223372036854775808)
                            9223372036854775808)
                      (LET* ((S (AS 'C (BITS 0 0 0) S))
                             (S (AS 'N (BITS 1 0 0) S))
                             (S (AS 'V (BITS 0 0 0) S)))
                            (AS 'Z (BITS 0 0 0) S))
                      (LET* ((S (AS 'C (BITS 1 0 0) S))
                             (S (AS 'N (BITS 0 0 0) S))
                             (S (AS 'V (BITS 0 0 0) S)))
                            (AS 'Z (BITS 0 0 0) S))))))

(DEFUN DO_CONST (S)
       (LET ((K (BITS (LOGIOR (ASH (AG 'OP2 S) 8) (AG 'OP3 S))
                      63 0)))
            (AS 'REGS
                (AS (AG 'OP1 S) K (AG 'REGS S))
                S)))

(DEFUN DO_MUL (S)
       (AS 'REGS
           (AS (AG 'OP1 S)
               (BITS (* (AG (AG 'OP2 S) (AG 'REGS S))
                        (AG (AG 'OP3 S) (AG 'REGS S)))
                     63 0)
               (AG 'REGS S))
           S))

(DEFUN DO_SUB (S)
       (AS 'REGS
           (AS (AG 'OP1 S)
               (BITS (- (AG (AG 'OP2 S) (AG 'REGS S))
                        (AG (AG 'OP3 S) (AG 'REGS S)))
                     63 0)
               (AG 'REGS S))
           S))

(DEFUN DO_SUBI (S)
       (AS 'REGS
           (AS (AG 'OP1 S)
               (BITS (- (AG (AG 'OP2 S) (AG 'REGS S))
                        (AG 'OP3 S))
                     63 0)
               (AG 'REGS S))
           S))

(DEFUN DO_B (S)
       (IF1 (LOG> (AG 'OP1 S) 127)
            (AS 'PC
                (BITS (+ (AG 'PC S) (- (AG 'OP1 S) 256))
                      9 0)
                S)
            (AS 'PC
                (BITS (+ (AG 'PC S) (AG 'OP1 S)) 9 0)
                S)))

(DEFUN DO_BEQ (S)
       (IF1 (LOG= (AG 'Z S) 1)
            (IF1 (LOG> (AG 'OP1 S) 127)
                 (AS 'PC
                     (BITS (+ (AG 'PC S) (- (AG 'OP1 S) 256))
                           9 0)
                     S)
                 (AS 'PC
                     (BITS (+ (AG 'PC S) (AG 'OP1 S)) 9 0)
                     S))
            S))

(DEFUN DO_BNE (S)
       (IF1 (LOG= (AG 'Z S) 0)
            (IF1 (LOG> (AG 'OP1 S) 127)
                 (AS 'PC
                     (BITS (+ (AG 'PC S) (- (AG 'OP1 S) 256))
                           9 0)
                     S)
                 (AS 'PC
                     (BITS (+ (AG 'PC S) (AG 'OP1 S)) 9 0)
                     S))
            S))

(DEFUN DO_BLS (S)
       (IF1 (LOGIOR1 (LOG= (AG 'C S) 0)
                     (LOG= (AG 'Z S) 1))
            (IF1 (LOG> (AG 'OP1 S) 127)
                 (AS 'PC
                     (BITS (+ (AG 'PC S) (- (AG 'OP1 S) 256))
                           9 0)
                     S)
                 (AS 'PC
                     (BITS (+ (AG 'PC S) (AG 'OP1 S)) 9 0)
                     S))
            S))

(DEFUN DO_BHI (S)
       (IF1 (LOG= (AG 'C S) 1)
            (IF1 (LOG> (AG 'OP1 S) 127)
                 (AS 'PC
                     (BITS (+ (AG 'PC S) (- (AG 'OP1 S) 256))
                           9 0)
                     S)
                 (AS 'PC
                     (BITS (+ (AG 'PC S) (AG 'OP1 S)) 9 0)
                     S))
            S))

(DEFUN DO_HALT (S)
       (AS 'PC (BITS (- (AG 'PC S) 1) 9 0) S))

(DEFUN DO_NOP (S) S)

(DEFUN
 DO_INST (S)
 (LET
  ((OPC (AG 'OPCODE S)))
  (IF1
   (LOG= OPC 1)
   (DO_ADD S)
   (IF1
    (LOG= OPC 2)
    (DO_ADDI S)
    (IF1
     (LOG= OPC 3)
     (DO_B S)
     (IF1
      (LOG= OPC 4)
      (DO_BEQ S)
      (IF1
       (LOG= OPC 5)
       (DO_BHI S)
       (IF1
        (LOG= OPC 6)
        (DO_BLS S)
        (IF1
          (LOG= OPC 7)
          (DO_BNE S)
          (IF1 (LOG= OPC 8)
               (DO_CMP S)
               (IF1 (LOG= OPC 9)
                    (DO_CMPI S)
                    (IF1 (LOG= OPC 10)
                         (DO_CONST S)
                         (IF1 (LOG= OPC 11)
                              (DO_MUL S)
                              (IF1 (LOG= OPC 12)
                                   (DO_NOP S)
                                   (IF1 (LOG= OPC 13)
                                        (DO_SUB S)
                                        (IF1 (LOG= OPC 14)
                                             (DO_SUBI S)
                                             (IF1 (LOG= OPC 15)
                                                  (DO_HALT S)
                                                  (IF1 (LOG= OPC 16)
                                                       (DO_LDR S)
                                                       (IF1 (LOG= OPC 17)
                                                            (DO_STR S)
                                                            S)))))))))))))))))))

(DEFUN LEG64STEP (S)
       (DO_INST (NEXTINST S)))

(DEFUN LEG64STEPS-LOOP-0 (I COUNT S)
       (DECLARE (XARGS :MEASURE (NFIX (- I 0))))
       (IF (AND (INTEGERP I) (> I 0))
           (LET ((S (LEG64STEP S)))
                (LEG64STEPS-LOOP-0 (- I 1) COUNT S))
           S))

(DEFUN LEG64STEPS (S COUNT)
       (LEG64STEPS-LOOP-0 COUNT COUNT S))

(DEFUN DOFACTO3 (N S)
       (LET* ((S (AS 'REGS (AS 0 N (AG 'REGS S)) S))
              (S (AS 'REGS
                     (AS 1 (BITS 1 63 0) (AG 'REGS S))
                     S))
              (K (BITS 0 9 0))
              (S (AS 'CMEM
                     (AS K
                         (BITS (LOGIOR (ASH (LOGAND 10 255) 24)
                                       (LOGAND N 255))
                               31 0)
                         (AG 'CMEM S))
                     S))
              (K (BITS (+ K 1) 9 0))
              (S (AS 'CMEM
                     (AS K
                         (BITS (LOGIOR (LOGIOR (ASH (LOGAND 10 255) 24)
                                               (ASH 1 16))
                                       1)
                               31 0)
                         (AG 'CMEM S))
                     S))
              (K (BITS (+ K 1) 9 0))
              (S (AS 'CMEM
                     (AS K
                         (BITS (LOGIOR (LOGIOR (ASH (LOGAND 9 255) 24)
                                               (ASH 1 8))
                                       0)
                               31 0)
                         (AG 'CMEM S))
                     S))
              (K (BITS (+ K 1) 9 0))
              (S (AS 'CMEM
                     (AS K
                         (BITS (LOGIOR (LOGIOR (ASH (LOGAND 6 255) 24)
                                               (ASH 4 16))
                                       0)
                               31 0)
                         (AG 'CMEM S))
                     S))
              (K (BITS (+ K 1) 9 0))
              (S (AS 'CMEM
                     (AS K
                         (BITS (LOGIOR (LOGIOR (LOGIOR (ASH (LOGAND 11 255) 24)
                                                       (ASH 1 16))
                                               (ASH 1 8))
                                       0)
                               31 0)
                         (AG 'CMEM S))
                     S))
              (K (BITS (+ K 1) 9 0))
              (S (AS 'CMEM
                     (AS K
                         (BITS (LOGIOR (ASH (LOGAND 14 255) 24) 1)
                               31 0)
                         (AG 'CMEM S))
                     S))
              (K (BITS (+ K 1) 9 0))
              (S (AS 'CMEM
                     (AS K
                         (BITS (LOGIOR (LOGIOR (ASH (LOGAND 9 255) 24)
                                               (ASH 1 8))
                                       0)
                               31 0)
                         (AG 'CMEM S))
                     S))
              (K (BITS (+ K 1) 9 0))
              (S (AS 'CMEM
                     (AS K
                         (BITS (LOGIOR (LOGIOR (ASH (LOGAND 7 255) 24)
                                               (ASH 252 16))
                                       0)
                               31 0)
                         (AG 'CMEM S))
                     S))
              (K (BITS (+ K 1) 9 0))
              (S (AS 'CMEM
                     (AS K
                         (BITS (LOGIOR (LOGIOR (ASH (LOGAND 2 255) 24)
                                               (ASH 1 8))
                                       0)
                               31 0)
                         (AG 'CMEM S))
                     S))
              (K (BITS (+ K 1) 9 0))
              (S (AS 'CMEM
                     (AS K
                         (BITS (LOGIOR (ASH (LOGAND 15 255) 24) 0)
                               31 0)
                         (AG 'CMEM S))
                     S)))
             (LEG64STEPS S (+ (+ 4 (* N 4)) 2))))

(DEFUN DOFACT (N S)
       (LET* ((S (AS 'REGS (AS 0 N (AG 'REGS S)) S))
              (S (AS 'REGS
                     (AS 1 (BITS 1 63 0) (AG 'REGS S))
                     S))
              (K (BITS 0 9 0))
              (S (AS 'CMEM
                     (AS K
                         (BITS (LOGIOR (ASH (LOGAND 10 255) 24)
                                       (LOGAND N 255))
                               31 0)
                         (AG 'CMEM S))
                     S))
              (K (BITS (+ K 1) 9 0))
              (S (AS 'CMEM
                     (AS K
                         (BITS (LOGIOR (LOGIOR (ASH (LOGAND 10 255) 24)
                                               (ASH 1 16))
                                       1)
                               31 0)
                         (AG 'CMEM S))
                     S))
              (K (BITS (+ K 1) 9 0))
              (S (AS 'CMEM
                     (AS K
                         (BITS (LOGIOR (LOGIOR (ASH (LOGAND 10 255) 24)
                                               (ASH 2 16))
                                       20)
                               31 0)
                         (AG 'CMEM S))
                     S))
              (K (BITS (+ K 1) 9 0))
              (S (AS 'CMEM
                     (AS K
                         (BITS (LOGIOR (LOGIOR (ASH (LOGAND 8 255) 24)
                                               (ASH 2 8))
                                       0)
                               31 0)
                         (AG 'CMEM S))
                     S))
              (K (BITS (+ K 1) 9 0))
              (S (AS 'CMEM
                     (AS K
                         (BITS (LOGIOR (LOGIOR (ASH (LOGAND 5 255) 24)
                                               (ASH 5 16))
                                       0)
                               31 0)
                         (AG 'CMEM S))
                     S))
              (K (BITS (+ K 1) 9 0))
              (S (AS 'CMEM
                     (AS K
                         (BITS (LOGIOR (ASH (LOGAND 9 255) 24) 0)
                               31 0)
                         (AG 'CMEM S))
                     S))
              (K (BITS (+ K 1) 9 0))
              (S (AS 'CMEM
                     (AS K
                         (BITS (LOGIOR (LOGIOR (ASH (LOGAND 4 255) 24)
                                               (ASH 3 16))
                                       0)
                               31 0)
                         (AG 'CMEM S))
                     S))
              (K (BITS (+ K 1) 9 0))
              (S (AS 'CMEM
                     (AS K
                         (BITS (LOGIOR (LOGIOR (LOGIOR (ASH (LOGAND 11 255) 24)
                                                       (ASH 1 16))
                                               (ASH 1 8))
                                       0)
                               31 0)
                         (AG 'CMEM S))
                     S))
              (K (BITS (+ K 1) 9 0))
              (S (AS 'CMEM
                     (AS K
                         (BITS (LOGIOR (ASH (LOGAND 14 255) 24) 1)
                               31 0)
                         (AG 'CMEM S))
                     S))
              (K (BITS (+ K 1) 9 0))
              (S (AS 'CMEM
                     (AS K
                         (BITS (LOGIOR (LOGIOR (ASH (LOGAND 3 255) 24)
                                               (ASH 251 16))
                                       0)
                               31 0)
                         (AG 'CMEM S))
                     S))
              (K (BITS (+ K 1) 9 0))
              (S (AS 'CMEM
                     (AS K
                         (BITS (LOGIOR (LOGIOR (ASH (LOGAND 2 251) 24)
                                               (ASH 1 8))
                                       0)
                               31 0)
                         (AG 'CMEM S))
                     S))
              (K (BITS (+ K 1) 9 0))
              (S (AS 'CMEM
                     (AS K
                         (BITS (LOGIOR (ASH (LOGAND 15 255) 24) 0)
                               31 0)
                         (AG 'CMEM S))
                     S)))
             (LEG64STEPS S (+ (+ 5 (* N 5)) 3))))

