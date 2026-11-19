# Open case, round 3: starting ideas

Status (2026-11-19). These are sketches by the coordinating AI (Claude). Nobody has checked
them. Each item says whether it is a proved lemma, a reduction, or only a plan.

The open case: non(N) < cof(N), c ≥ ℵ_3, every universally null set has size < cof(N).
Target: either a ZFC proof of add(UN) ≤ add(N), or a model of add(N) < add(UN).

Notation as in `notes/partial-results.md`. λ is the product measure on 2^ω. "Admissible
measure" means a finite Borel measure on 2^ω that vanishes on singletons.

## 1. Fibre lemma (proof sketch, short)

**Lemma F.** Let φ be a Borel map on a Borel set D ⊆ 2^ω, X ⊆ D, P ∈ UN, φ[X] ⊆ P. If every
fibre X ∩ φ^{-1}(p), p ∈ P, is universally null, then X is universally null.

*Sketch.* Let μ be admissible and ν the image of μ↾D under φ. Write ν = ν_c + ν_a with ν_c
vanishing on singletons and ν_a concentrated on a countable set A. Take a Borel B ⊇ P with
ν_c(B) = 0. Then X ⊆ φ^{-1}(B ∖ A) ∪ ⋃_{p ∈ A ∩ P} (X ∩ φ^{-1}(p)). The first set has
μ-measure ν(B ∖ A) = ν_c(B ∖ A) = 0. The rest is a countable union of universally null sets.

Lemma 3 of the note is the case of one-point fibres. Lemma F does not by itself give larger
sets: a tree of finite height over universally null sets of size ≤ κ still has ≤ κ points.

## 2. Translates (trivial reduction)

A translate of a universally null set is universally null. So

  add(UN) ≤ min{ |X| : there is G ∈ UN with X + G ∉ N }.

Compare the transitive additivity add*(N) = min{ |X| : there is G ∈ N with X + G ∉ N }.
The literature states add(N) = min{b, add*(N)} (Pawlikowski; Bartoszyński–Judah, Section 2.7).
**This citation is from memory and must be checked before use.**

**Plan Z.** Prove in ZFC both
 (Z1) add(UN) ≤ b, and
 (Z2) for some X that witnesses add*(N) there is a universally null G with X + G ∉ N.
Together with the cited formula this gives add(UN) ≤ add(N) and settles the problem.
Neither (Z1) nor (Z2) is proved. Theorem A gives only add(UN) ≤ d.

Note: X + G ∉ N forces |G| ≥ non(N) when |X| < non(N). So G must be a universally null set
of size at least non(N), such as a Grzegorek set.

## 3. Self-referential Grzegorek scheme (plan, with known obstacles)

Recall the proof of Grzegorek's theorem as formalised in `AddUN/Grzegorek.lean`. Let H be a
Borel subset of 2^ω × Codes with every section H_y null and every null set inside a section.
Let Z = {z_α : α < κ}, κ = non(N), be not null, and let y_α be distinct codes with
{z_β : β < α} ⊆ H_{y_α}. Then Y = {y_α} is universally null. The proof: if μ is admissible,
Fubini gives a co-null set of z with μ{y : z ∈ H_y} = 0. Some z_β is in it. So
{y_α : α > β} is μ-null, and {y_α : α ≤ β} has size < non(N).

**Scheme GS.** Let (Φ_i)_{i ∈ I} be Borel maps into the code space. Suppose there are a set
Z = {z_α : α < non(N)} that is not null and indices i_α ∈ I such that, with
y_α = Φ_{i_α}(z_α):
 (a) {z_β : β < α} ⊆ H_{y_α} for every α, and
 (b) each Φ_i is injective on Z_i = {z_α : i_α = i}.
Then Y = {y_α} is universally null, each Z_i is universally null by Lemma 3, and
Z = ⋃_i Z_i is not null. Hence add(UN) ≤ |I|.

So GS with |I| = add(N) would settle the problem. In words: each point z_α, read with one of
add(N) keys, must encode a null set that covers all earlier points.

The natural keys are the maps φ_f of the coding lemma (Lemma 2), f in an unlocalised family
F of size add(N), or translations by a set X that is not N-additive. The coding lemma gives:
for every code c the set R_c = ⋃_{f ∈ F} φ_f^{-1}(c) meets every compact set of positive
measure. So at each stage α the set R_α of admissible points z_α has full outer measure.

**Obstacles found.**
 (O1) Pigeonhole. For a fixed point w, the stages α at which w is admissible are bounded in
   non(N) when non(N) is regular and > |I|: otherwise one key covers all of Z by one null
   set. So the sets R_α decrease to ∅.
 (O2) Transversal. No family of fewer than non(N) null sets can cover every set of size
   < non(N). So admissibility must depend on z_α, not only on the key.
 (O3) Non-nullness in non(N) steps. The recursion has only non(N) steps and cannot meet a
   cofinal family of cof(N) compact sets. One must force Z to be non-null another way, for
   example by keeping z_α in the orbit of a prescribed point t_α under fewer than add(N)
   null-preserving maps. But a union of add(N) null sets need not contain t_α.
 (O4) Length cof(N). With cof(N) steps Z can meet every positive compact set, but then the
   initial segments of Z are not null and those of Y have size ≥ non(N). The Fubini step then
   needs: for every co-null C there is a set D ⊆ Z ∩ C of size < add(N) such that all but
   fewer than non(N) of the coded sets H_{y_α} meet D.

Either a way round (O3)/(O4) or a proof that GS cannot work in ZFC would be progress.

## 4. What earlier rounds ruled out

See "What is still open" in `notes/partial-results.md` and `agent-logs/round2.json`:
leaf devices need at least cov(M) maps; the method of Theorem A cannot go below d; the
selector cardinal is cof(N).
