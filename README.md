# ICL-UROP---LeanProver

## Introduction

This is a personal project on solving an analysis question on
convergent series. The question is:
Suppose that a sequence a_n ≥ 0 ∀ n
and converges to a ∈ [0,1). 
Prove that ![equation](http://www.sciweavers.org/tex2img.php?eq=%5Csum_%7Bn%3D1%7D%5E%5Cinfty%20a_n%5En&bc=White&fc=Black&im=jpg&fs=12&ff=modern&edit=0) converges.

## Proof

The approach here is to use the theorem: *if a sequence is monotonically
increasing and bounded above, then it converges*.
Therefore the problem is firstly divided into two big parts:
1. Prove the theorem, named as `bounded_above_and_increasing_func_converges`.
2. Prove the question, name as `series_of_root_numbers_converges`.

Only the last lemma (the longest lemma in the code) 
is directly tackling the question. 
All the previous lemmas are used to prove the theorem.

Regarding the first step, I further broke it
down and proved another lemma: *if a sequence is increasing and has a
supremum, then it converges to the supremum*. Then using this lemma to prove
the theorem.

Regarding the second step, the proof is broken down into two parts:
the sequence is monotonically increasing, and it is bounded above.
The core of the second part of the proof is the calc block as marked in the
code.

# Credits

Thanks to Professor Kevin Buzzard to exposing me to the world of formal proof
using Lean, and all the other people in the Zulip chat that helped me along
the way. Special thanks to JasonKY who provided two lemmas regarding summations
which greatly assisted my proof, as commented in the code.
