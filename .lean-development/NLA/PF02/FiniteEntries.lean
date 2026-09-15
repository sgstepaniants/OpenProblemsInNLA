/- Direct finite-vector evaluation lemmas for the PF-02 exact certificates.
These are definitional identities, proved by the kernel with rfl. The tail-index
form avoids rewriting vector notation back and forth through Fin.cons.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology. Apache 2.0; AI-assisted. -/
import Mathlib.Data.Fin.VecNotation

set_option autoImplicit false
namespace NLA.PF02

lemma vector_at_two {α : Type*} {m : ℕ} (x : α) (v : Fin m.succ.succ → α) :
    Matrix.vecCons x v (2 : Fin m.succ.succ.succ) = v 1 := rfl

lemma vector_at_three {α : Type*} {m : ℕ} (x : α) (v : Fin m.succ.succ.succ → α) :
    Matrix.vecCons x v (3 : Fin m.succ.succ.succ.succ) = v 2 := rfl

lemma vector_at_four {α : Type*} {m : ℕ} (x : α)
    (v : Fin m.succ.succ.succ.succ → α) :
    Matrix.vecCons x v (4 : Fin m.succ.succ.succ.succ.succ) = v 3 := rfl

lemma vector_at_five {α : Type*} {m : ℕ} (x : α)
    (v : Fin m.succ.succ.succ.succ.succ → α) :
    Matrix.vecCons x v (5 : Fin m.succ.succ.succ.succ.succ.succ) = v 4 := rfl

end NLA.PF02
