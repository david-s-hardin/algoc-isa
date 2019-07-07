;; Copyright (C) 2019, David S. Hardin
;; License: A 3-clause BSD license.  See the LICENSE file in this directory.

;; Based on demo-fact.lisp
; Copyright (C) 2014, ForrestHunt, Inc.
; Written by Matt Kaufmann and J Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Adapted by Matt Kaufmann from J Moore's file, basic-demo.lsp.

(in-package "RTL")

; -----------------------------------------------------------------
; Demo of Def-Semantics and Def-Projection

; NOTE: See the following included book, demo-fact-preamble, for important
; comments pertaining to this demo.

(include-book "fact-leg64-preamble")

(set-verify-guards-eagerness 0) ; local to the book above

(DEFTHM SEM-0-CORRECT-AUX-1
  (IMPLIES
       (AND (EQUAL (AG 0 (AG 'REGS S)) 1)
            (FACT-ROUTINE-LOADEDP S)
            (INTEGERP (AG 1 (AG 'REGS S)))
            (<= 0 (AG 1 (AG 'REGS S)))
            (< (AG 1 (AG 'REGS S))
               18446744073709551616)
            (EQUAL (AG 'PC S) 0))
       (EQUAL (LEG64STEPN S 5)
              (AS 'C
                  1
                  (AS 'N
                      0
                      (AS 'V
                          0
                          (AS 'Z
                              0
                              (AS 'PC
                                  0
                                  (AS 'OP1
                                      251
                                      (AS 'OP2
                                          0
                                          (AS 'OP3
                                              0
                                              (AS 'REGS
                                                  (AS 0 0 (AG 'REGS S))
                                                  (AS 'OPCODE 3 S))))))))))))
  :INSTRUCTIONS (:PROMOTE (:DIVE 1)
                          (:REWRITE LEG64STEPN)
                          :S (:REWRITE LEG64STEPN)
                          :S (:REWRITE LEG64STEPN)
                          :S (:REWRITE LEG64STEPN)
                          :S (:REWRITE LEG64STEPN)
                          :TOP
                          :S :BASH))

(DEFTHM SEM-0-CORRECT-AUX-2
 (IMPLIES
  (AND
   (INTEGERP C0)
   (<= 0 C0)
   (FACT-ROUTINE-LOADEDP S)
   (INTEGERP (AG 0 (AG 'REGS S)))
   (<= 1 (AG 0 (AG 'REGS S)))
   (< (AG 0 (AG 'REGS S))
      18446744073709551616)
   (INTEGERP (AG 1 (AG 'REGS S)))
   (<= 0 (AG 1 (AG 'REGS S)))
   (< (AG 1 (AG 'REGS S))
      18446744073709551616)
   (NOT (EQUAL (LOGAND 9223372036854775808 (AG 0 (AG 'REGS S)))
               9223372036854775808))
   (EQUAL
    (LEG64STEPN
     (AS
        'C
        1
        (AS 'N
            0
            (AS 'V
                0
                (AS 'Z
                    0
                    (AS 'PC
                        0
                        (AS 'OP1
                            251
                            (AS 'OP2
                                0
                                (AS 'OP3
                                    0
                                    (AS 'REGS
                                        (AS 0 (+ -1 (AG 0 (AG 'REGS S)))
                                            (AS 1
                                                (BITS (* (AG 0 (AG 'REGS S))
                                                         (AG 1 (AG 'REGS S)))
                                                      63 0)
                                                (AG 'REGS S)))
                                        (AS 'OPCODE 3 S))))))))))
     C0)
    S0)
   (EQUAL (AG 'PC S) 0))
  (EQUAL (LEG64STEPN S (+ 5 C0)) S0))
 :INSTRUCTIONS (:PROMOTE (:DIVE 1)
                         (:REWRITE LEG64STEPN-PLUS--THM)
                         (:DIVE 1)
                         (:REWRITE LEG64STEPN)
                         :S (:REWRITE LEG64STEPN)
                         :S (:REWRITE LEG64STEPN)
                         :S (:REWRITE LEG64STEPN)
                         :S (:REWRITE LEG64STEPN)
                         :S
                         :TOP :BASH))

(DEFTHM SEM-0-CORRECT-AUX-3
 (IMPLIES
  (AND
   (INTEGERP C0)
   (<= 0 C0)
   (FACT-ROUTINE-LOADEDP S)
   (INTEGERP (AG 0 (AG 'REGS S)))
   (<= 1 (AG 0 (AG 'REGS S)))
   (< (AG 0 (AG 'REGS S))
      18446744073709551616)
   (INTEGERP (AG 1 (AG 'REGS S)))
   (<= 0 (AG 1 (AG 'REGS S)))
   (< (AG 1 (AG 'REGS S))
      18446744073709551616)
   (EQUAL (LOGAND 9223372036854775808 (AG 0 (AG 'REGS S)))
          9223372036854775808)
   (EQUAL
    (LEG64STEPN
     (AS
        'C
        0
        (AS 'N
            1
            (AS 'V
                0
                (AS 'Z
                    0
                    (AS 'PC
                        0
                        (AS 'OP1
                            251
                            (AS 'OP2
                                0
                                (AS 'OP3
                                    0
                                    (AS 'REGS
                                        (AS 0 (+ -1 (AG 0 (AG 'REGS S)))
                                            (AS 1
                                                (BITS (* (AG 0 (AG 'REGS S))
                                                         (AG 1 (AG 'REGS S)))
                                                      63 0)
                                                (AG 'REGS S)))
                                        (AS 'OPCODE 3 S))))))))))
     C0)
    S0)
   (EQUAL (AG 'PC S) 0))
  (EQUAL (LEG64STEPN S (+ 5 C0)) S0))
 :INSTRUCTIONS (:PROMOTE (:DIVE 1)
                         (:REWRITE LEG64STEPN-PLUS--THM)
                         (:DIVE 1)
                         (:REWRITE LEG64STEPN)
                         :S (:REWRITE LEG64STEPN)
                         :S (:REWRITE LEG64STEPN)
                         :S (:REWRITE LEG64STEPN)
                         :S (:REWRITE LEG64STEPN)
                         :S
                         :TOP :BASH))


; Here is the command that causes Codewalker to explore our program and
; create a semantic function, named SEM-0, since the initial pc is 0.

(def-semantics
  :init-pc 0
  :focus-regionp nil
  :root-name nil
  :hyps+ ((fact-routine-loadedp s)  ;;(equal (ag 'CMEM s) *program1*)
;;        (unsigned-byte-p 10 (ag 'pc s))
          (integerp (ag 0 (ag 'REGS s)))
          (>= (ag 0 (ag 'REGS s)) 1) 
;;          (<= (ag 0 (ag 'REGS s)) 20)
          (< (ag 0 (ag 'REGS s)) 18446744073709551616)
          (integerp (ag 1 (ag 'REGS s)))
          (<= 0 (ag 1 (ag 'REGS s)))
          (< (ag 1 (ag 'REGS s)) 18446744073709551616)
          (< (ag 'PC s) (len (ag 'CMEM s)))
;;          (<= (len (ag 'REGS s)) 256)
          )
  :annotations nil
;;  :annotations ((clk-0 (declare (xargs :measure (clk-0-measure s))))
;;                (sem-0 (declare (xargs :measure (clk-0-measure s)))))
  )

;; ??? The following def-projection fails, but it emits a candidate fn1-loop
;; (see below) that can easily be modified to eliminate all mentions of
;; state s.  Add a simple :measure, and it can be admitted into ACL2.
;; 
;; ??? If you issue an (in-theory (enable fact-routine-loadedp)) before
;; executing this, the def

;; (def-projection
;;   :new-fn FN1-LOOP
;;   :projector (ag 1 (ag 'regs s))
;;   :old-fn ACL2::SEM-0
;;   :hyps+ nil ;; ((fact-routine-loadedp s))
;; )

;; ??? Failed def-projection emits this function.  We easily remove
;; the remaining reference to the state vector, S

(DEFUN FN1-LOOP (PC ACL2::REGS0 ACL2::REGS1)
  (declare (xargs :measure (nfix ACL2::REGS0)))
 (IF
  (IF (NATP PC)
      (IF (NATP ACL2::REGS0)
          (NATP ACL2::REGS1)
          'NIL)
      'NIL)
  ;;(IF
   ;;(FACT-ROUTINE-LOADEDP S)
   (IF
    (INTEGERP ACL2::REGS0)
    (IF
     (< ACL2::REGS0 '1)
     ACL2::REGS1
     (IF
      (< ACL2::REGS0 '18446744073709551616)
      (IF
       (INTEGERP ACL2::REGS1)
       (IF
        (< ACL2::REGS1 '0)
        ACL2::REGS1
        (IF
         (< ACL2::REGS1 '18446744073709551616)
         (IF
           (ACL2-NUMBERP PC)
           (IF (< PC '7)
               (IF (EQUAL (BINARY-LOGAND '9223372036854775808
                                         ACL2::REGS0)
                          '9223372036854775808)
                   (FN1-LOOP '0
                             (IF (ACL2-NUMBERP ACL2::REGS0)
                                 (BINARY-+ '-1 ACL2::REGS0)
                                 '-1)
                             (IF (ACL2-NUMBERP ACL2::REGS1)
                                 (IF (ACL2-NUMBERP ACL2::REGS0)
                                     (BITS (BINARY-* ACL2::REGS0 ACL2::REGS1)
                                           '63
                                           '0)
                                     '0)
                                 '0))
                   (FN1-LOOP '0
                             (IF (ACL2-NUMBERP ACL2::REGS0)
                                 (BINARY-+ '-1 ACL2::REGS0)
                                 '-1)
                             (IF (ACL2-NUMBERP ACL2::REGS1)
                                 (IF (ACL2-NUMBERP ACL2::REGS0)
                                     (BITS (BINARY-* ACL2::REGS0 ACL2::REGS1)
                                           '63
                                           '0)
                                     '0)
                                 '0)))
               ACL2::REGS1)
           (IF (EQUAL (BINARY-LOGAND '9223372036854775808
                                     ACL2::REGS0)
                      '9223372036854775808)
               (FN1-LOOP '0
                         (IF (ACL2-NUMBERP ACL2::REGS0)
                             (BINARY-+ '-1 ACL2::REGS0)
                             '-1)
                         (IF (ACL2-NUMBERP ACL2::REGS1)
                             (IF (ACL2-NUMBERP ACL2::REGS0)
                                 (BITS (BINARY-* ACL2::REGS0 ACL2::REGS1)
                                       '63
                                       '0)
                                 '0)
                             '0))
               (FN1-LOOP '0
                         (IF (ACL2-NUMBERP ACL2::REGS0)
                             (BINARY-+ '-1 ACL2::REGS0)
                             '-1)
                         (IF (ACL2-NUMBERP ACL2::REGS1)
                             (IF (ACL2-NUMBERP ACL2::REGS0)
                                 (BITS (BINARY-* ACL2::REGS0 ACL2::REGS1)
                                       '63
                                       '0)
                                 '0)
                             '0))))
         ACL2::REGS1))
       ACL2::REGS1)
      ACL2::REGS1))
    ACL2::REGS1)
;;   ACL2::REGS1)
  '0))


(defun ! (n)
  (if (zp n)
      1
      (* n (! (- n 1)))))


(defthm fn1-loop-is-!-gen
  (implies (and (natp r0) (natp r1) (< r0 (expt 2 64))
                (< r1 (expt 2 64)))
           (equal (fn1-loop 0 r0 r1)
                  (bits (* r1 (! r0)) 63 0))))

(defun fn1 (r0)
    (fn1-loop 0 r0 1))

(defthm fn1-is-!
  (implies (and (natp r0) (< r0 (expt 2 64)))
           (equal (fn1 r0)
                  (bits (! r0) 63 0))))

; And because of all we know, we can immediately relate it to the
; result of running the code:


(defthm reg-1-of-program1-is-n!
  (implies
  (AND (FACT-ROUTINE-LOADEDP S)
       (INTEGERP (AG 0 (AG 'REGS S)))
       (< 0 (AG 0 (AG 'REGS S)))
       (< (AG 0 (AG 'REGS S)) (expt 2 64))
       (INTEGERP (AG 1 (AG 'REGS S)))
       (<= 0 (AG 1 (AG 'REGS S)))
       (< (AG 1 (AG 'REGS S)) (expt 2 64))
       (EQUAL (AG 'PC S) 0))
   (equal (ag 1 (ag 'regs (leg64stepn s (acl2::clk-0 s))))
          (bits (* (ag 1 (ag 'regs s)) (! (ag 0 (ag 'regs s)))) 63 0))))
