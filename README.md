# ICL-UROP---LeanProver

## Introduction

This is a personal project on solving an analysis question on
convergent series. The question is:
Suppose that a sequence a_n ≥ 0 ∀ n
and converges to a ∈ [0,1). 
Prove that ![equation](http://www.sciweavers.org/tex2img.php?eq=%5Csum_%7Bn%3D1%7D%5E%5Cinfty%20a_n%5En&bc=White&fc=Black&im=jpg&fs=12&ff=modern&edit=0) converges.

## Proof

The approach here is to use the theorem that, if a sequence is monotonically
increasing and bounded above, then it converges.
Therefore the problem is firstly devided into two big parts:
1. Prove the theorem.
2. Prove the question.

Only the last lemma (the longest lemma in the code) 
is directly tackling the question. 
All the previous lemmas are used to prove the theorem.
