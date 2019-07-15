;; Copyright (C) 2019, David S. Hardin
;; License: A 3-clause BSD license.  See the LICENSE file in this directory.

;; "Staging" book between the automatically-generated leg64 book and Codewalker.

(IN-PACKAGE "RTL")

(include-book "leg64")

(include-book "rtl/rel11/lib/bits" :dir :system)

(include-book "arithmetic-5/top" :dir :system)

;; Unfortunately, there are some conflicts between arithmetic-5 and this library
;; (especially the "basic" book) that can severely slow down some proofs.  Much of 
;; this can be avoided by disabling the following lemmas:

(in-theory #!acl2(disable |(mod (+ x y) z) where (<= 0 z)| |(mod (+ x (- (mod a b))) y)|
                          |(mod (mod x y) z)| |(mod (+ x (mod a b)) y)| mod-cancel-*-const
			  cancel-mod-+ reduce-additive-constant-< ash-to-floor |(floor x 2)|
			  |(equal x (if a b c))| |(equal (if a b c) x)| |(logior 1 x)|
			  mod-theorem-one-b |(mod (- x) y)|))

(DEFTHM BITS-UPPER-BOUND
  (IMPLIES (AND (INTEGERP I) (INTEGERP J))
           (< (BITS X I J) (EXPT 2 (1+ (- I J)))))
  :INSTRUCTIONS
  (:PROMOTE
   (:CLAIM (AND (NATP (BITS X I J))
                (< (BITS X I J) (EXPT 2 (1+ (- I J)))))
           :HINTS (("Goal" :USE (:INSTANCE BITS-BOUNDS))))
   :BASH))

(DEFTHM BITS-UPPER-BOUND-LE
 (IMPLIES (AND (INTEGERP I) (INTEGERP J) (<= 0 I) (>= i j))
          (<= (BITS X I j) (1- (EXPT 2 (1+ (- I J))))))
 :INSTRUCTIONS
 (:PROMOTE (:CLAIM (INTEGERP (EXPT 2 (1+ (- I J)))))
           (:CLAIM (< (BITS X I J) (EXPT 2 (1+ (- I J))))
                   :HINTS (("Goal" :USE (:INSTANCE BITS-UPPER-BOUND))))
           :BASH)
  :rule-classes ((:forward-chaining :trigger-terms ((BITS X I J))) :rewrite))


(DEFTHM BITS-ELIM--THM
  (IMPLIES
   (AND
    (INTEGERP I)
    (INTEGERP J)
    (< 0 J)
    (<= 0 I)
    (< I (EXPT 2 (1+ J))))
   (EQUAL (BITS I J 0) I))
  :INSTRUCTIONS
  (:PROMOTE
   (:DIVE 1)
   (:REWRITE BITS)
   (:= (FL (* (MOD I (EXPT 2 (+ 1 J)))
              (/ (EXPT 2 0)))))
   (:DIVE 1 2)
   (:= 1)
   :UP
   (:CLAIM (INTEGERP (MOD I (EXPT 2 (+ 1 J)))))
   (:REWRITE ACL2::|arith (* x 1)|)
   :UP (:REWRITE FL)
   (:REWRITE ACL2::|(floor x 1)|)
   (:REWRITE (:REWRITE ACL2::MOD-X-Y-=-X . 3))
   :TOP :BASH))


;; Codewalker requires the 'state' parameter to be the first parameter; for the 
;; rac-generated steps primitive (leg64steps-loop-0) called by leg64steps, the
;; state parameter is the last parameter.  Thus, we rewrite leg64steps-loop-0
;; slightly, and call the result leg64stepn.

(DEFUN LEG64STEPN (S N)
 (DECLARE (XARGS :MEASURE (NFIX N)))
       (IF (AND (INTEGERP N) (> N 0))
           (LET ((S (LEG64STEP S)))
                (LEG64STEPN S (- N 1)))
           S))

;; Justification for leg64stepsn

(defthmd leg64stepn-eq-leg64steps-aux--thm
  (= (leg64stepn s i) (leg64steps-loop-0 i n s))
  :hints (("Goal" :in-theory (disable leg64step))))

(DEFTHMD LEG64STEPN-EQ-LEGSTEPS--THM
   (= (LEG64STEPN S N) (LEG64STEPS S N))
   :INSTRUCTIONS
   ((:DIVE 2)
    (:REWRITE LEG64STEPS)
    :TOP
    (:PROVE
         :HINTS (("Goal" :USE (:INSTANCE LEG64STEPN-EQ-LEG64STEPS-AUX--THM
                                         (I N)))))))


(defthm leg64stepn-plus--thm
  (implies (and (integerp c1) (<= 0 c1)
                (integerp c2) (<= 0 c2))
           (= (leg64stepn s (+ c1 c2))
              (leg64stepn (leg64stepn s c1) c2)))
  :hints (("Goal" :in-theory (disable leg64step))))

(in-theory (enable bits-bits-prod))
