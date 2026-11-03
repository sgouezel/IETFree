/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.TopBotFormalism
public import IETFree.RauzyVeech.Affine

/-!
# Transport of the a.e. rigidity statement along `ofPerm`

The rigidity statement is proved for the
two-bijection datum `P = IETDatum₂.ofPerm π`, i.e. the single-permutation datum written with the
identity as bottom order; the source's single-permutation form is `mkIET1' lam π h`.  Nothing in
this file is specific to `d ≥ 2`: only `[NeZero d]` is needed, as in the statement of
`veechRigidity` (`IETFree/Pair/Irreducible.lean`; the case `d = 1` is separate,
`Rigidity/DimOne.lean`).
The transport is purely a rewriting:

* `simplexVolumeOn_fin d` identifies the measure `simplexVolumeOn (Fin d)` with the copied
  `simplexVolume d`;
* `IETDatum₂.ofPerm_toIET` identifies the exchange `(ofPerm π).toIET lam` with `mkIET1' lam π h`
  for `lam ∈ simplexOn (Fin d)`, which holds a.e. (`ae_mem_simplexOn_of_nonempty`);
* `IETDatum₂.coe_mkIET1'` shows that the underlying function of `mkIET1' lam π h` is
  `mkIETFun lam π 0`.

The hypothesis is an a.e. statement for the datum `ofPerm π`; the conclusion is the a.e. statement
for the source's single-permutation form, both for the exchange as a bundled `IET 0 1`.  This is one
of the two halves of the proof of `veechRigidity`.
-/

@[expose] public section

open MeasureTheory Filter

namespace IETFree.Rigidity

/-- **Transport of the a.e. rigidity statement from the datum `ofPerm π` to the source's
`mkIET1' lam π h`.**  This is the only place where the two-sided combinatorial datum is left
behind: `(ofPerm π).toIET lam` *is* `mkIET1' lam π h` (`IETDatum₂.ofPerm_toIET`), whose function is
`mkIETFun lam π 0`. -/
theorem ae_isRigidByTranslations_mkIET1 {d : ℕ} [NeZero d] (π : Equiv.Perm (Fin d))
    (h : ∀ᵐ lam ∂(simplexVolumeOn (Fin d)),
      IsRigidByTranslations ((IETDatum₂.ofPerm π).toIET lam)) :
    ∀ᵐ lam ∂(simplexVolume d), ∀ (hm : lam ∈ simplex d),
      IsRigidByTranslations (mkIET1' lam π hm) := by
  rw [← simplexVolumeOn_fin d]
  filter_upwards [h, ae_mem_simplexOn_of_nonempty (α := Fin d)] with lam hl hmem hm
  rw [← IETDatum₂.ofPerm_toIET π hmem]
  exact hl

end IETFree.Rigidity

end
