# Safety from Projection: Design Document

**Date:** 2026-02-23
**Theorem:** If `G ↾ Δ` then `safe Δ` (any projected context is safe).

## Overview

We prove that the projection of a well-formed global type onto a local context guarantees safety. Safety means that at every reachable state, whenever one participant can send to another and that other can receive, they can synchronize.

The proof uses a **projection-preserving simulation up to subtyping**: we track a global type alongside the local context through reductions, showing that the projection relationship (relaxed to `⊑`) is maintained.

## Key Definitions (existing)

```
safe Δ₀       = ∀ {Δ₁} → Δ₀ →₂* Δ₁ → SafeState Δ₁
SafeState Δ₀  = ∀ {p q U U' Δp Δq} → (p sends to q) → (q receives from p) → CanSync₂ Δ₀ p q U
G ↾ Δ         = ∀ p → G ↾[ p ] (Δ p)
Δ₀ ⊑ G        = Σ Δ (λ Δ' → (G ↾ Δ') × (Δ₀ ≤Δ Δ'))
```

## Proof Architecture

### New Lemmas

#### 1. `safeState-from-↾` (SafeState from exact projection)

```agda
safeState-from-↾ : ∀ {G Δ₀} → G ↾ Δ₀ → SafeState Δ₀
```

**Proof strategy:** Given `G ↾ Δ₀`, p can send to q, and q can receive from p, analyze the projection rules to find a matching synchronization.

Case analysis on `out↾ (G↾Δ₀ p)` (what projection rule produced p's local type):
- **PR1 (p is sender in msg p q b G'):** Then `G` has `msg p q b G'` at top. Projection of q via PR2 gives `recv p b Tq`. Synchronization on `obsBase b` exists.
- **PR3 (p uninvolved in msg s t b G'):** The send capability passes through to the sub-projection of G'. Recurse (the global type decreases structurally).
- **PR4 (p is sender in choice p q bs):** Projection of q via PR5 gives `bra p lbs`. The label l from p's selection is present in q's branch table.
- **PR6 (p uninvolved in choice, merged):** The send capability comes from the merged type. Need to trace it back to a branch projection and the underlying global structure.
- **PR7/PR8 (mu):** Unfold and recurse.

Termination: structural decrease on the global type (well-formedness guarantees guardedness of mu).

Coinductive concern: We only *consume* (force/observe) coinductive projections; we don't produce coinductive output. SafeState is a plain proposition.

#### 2. `merge-≤-branch` (merged type is subtype of each branch)

```agda
merge-≤-branch : ∀ {M T l Tₗ} → M Π T → lookupM l M ≡ just Tₗ → T ≤ Tₗ
```

**Proof strategy:** Coinduction on `M Π T`. At each merge step:
- **M1 (singleton end):** `T = end`, `Tₗ = end`, trivially `end ≤ end`.
- **M2 (unfold):** Unfold one mu in the merge set, recurse on the delayed sub-proof.
- **M3 (strip send heads):** All branches have `send q b Tᵢ`, merged is `send q b T'`. By IH, `T' ≤ Tᵢ` for each branch's continuation. Subtyping gives `send q b T' ≤ send q b Tₗ` via s-send.
- **M4 (strip recv heads):** Symmetric to M3 with s-recv.
- **M5 (sel, intersect domains):** Merged `sel q bs` has domain = intersection of branch domains. Each branch `sel q bsᵢ` has domain ⊇ merged domain. Subtyping `sel q bs ≤ sel q bsᵢ` via s-sel (sel is covariant: fewer options in subtype).
- **M6 (bra, union domains):** Merged `bra q bs` has domain = union. Each branch `bra q bsᵢ` has domain ⊆ merged domain. Subtyping `bra q bs ≤ bra q bsᵢ` via s-bra (bra is contravariant: more options in subtype).

Direction: `T ≤ Tₗ` because:
- Selection structure is unchanged by merging
- Branching may gain branches (union), making merged type a subtype (contravariant)

#### 3. `sim-↾` (exact projection preserved up to ≤Δ by →₂)

```agda
sim-↾ : ∀ {G Δ₁ Δ₁' ι}
       → G ↾ Δ₁
       → Δ₁ -[ ι ]→₂ Δ₁'
       → Σ Global₀ (λ G' → Σ Δ (λ Δ₂ →
           (G →ᵍ* G') × (G' ↾ Δ₂) × (Δ₁' ≤Δ Δ₂)))
```

**Proof strategy:** Given `G ↾ Δ₁` and a synchronous step `Δ₁ -[ p ↝⟨ U ⟩ q ]→₂ Δ₁'`:

1. From `G ↾[ p ] (Δ₁ p)` and p's send action, identify the global type structure.
2. Construct the corresponding global step `G →ᵍ* G'`.
3. Show `G' ↾ Δ₂` for some `Δ₂`:
   - For involved participants (p, q): their projections step correspondingly.
   - For uninvolved r: `Δ₁'(r) = Δ₁(r)` (unchanged by sync), and `Δ₂(r)` may differ from `Δ₁(r)` due to merge (choice case). Use `merge-≤-branch` to get `Δ₁'(r) ≤ Δ₂(r)`.

Cases by global type structure:
- **msg p q b G':** Direct GR1 step. Projections for p (PR1→continuation), q (PR2→continuation), r (PR3→same sub-projection). No merge issue. `Δ₁' = Δ₂`.
- **msg s t b G' (p,q uninvolved in outer msg):** Use GR2 to commute the step through. Recurse on the sub-global type.
- **choice p q bs:** GR4 step selecting branch l. For uninvolved r, use `merge-≤-branch`.
- **choice s t bs (p,q uninvolved):** GR5 to commute through. Recurse on branches.
- **mu body:** GR3 to unfold. Recurse.

#### 4. `safe-from-↾` (main theorem)

```agda
safe-from-↾ : ∀ {G Δ₀} → G ↾ Δ₀ → safe Δ₀
```

**Proof strategy:** Given `G ↾ Δ₀` and `Δ₀ →₂* Δ₂`, show `SafeState Δ₂`.

Walk the `→₂*` chain maintaining invariant `Δᵢ ⊑ Gᵢ`:
- Base: `Δ₀ ⊑ G` (with `Δ₀ ≤Δ Δ₀` by reflexivity).
- Step: Use `sim-⊑` (composed from `stepSim≤` + `sim-↾` + `≤-trans-ctx`).
- At final state: `safeState-from-⊑ = safeStateDownward ∘ safeState-from-↾`.

### Existing Lemmas Reused

| Lemma | Location | Purpose |
|-------|----------|---------|
| `stepSim≤` | Theory.LocalSemanticProperties | Lift local step through ≤Δ |
| `safeStateDownward` | Theory.LocalSemanticProperties | SafeState downward-closed under ≤Δ |
| `≤-trans-ctx` | Subtyping.SessionSubtypingProperties | Transitivity of ≤Δ |

### Dependency Graph

```
safe-from-↾
  ├── safeState-from-⊑
  │     ├── safeState-from-↾  (NEW)
  │     └── safeStateDownward  (EXISTS)
  └── sim-⊑
        ├── stepSim≤           (EXISTS)
        ├── sim-↾              (NEW)
        │     └── merge-≤-branch  (NEW)
        └── ≤-trans-ctx        (EXISTS)
```

## File Organization

New file: `Theory/ProjectionSafety.agda`
- Contains all 4 new lemmas
- Imports from Theory.MergeProjection, Theory.ProjectionProperties, Theory.LocalSemanticProperties

## Open Questions

1. **Termination of `safeState-from-↾`:** May need well-founded recursion on global type structure rather than relying on structural termination, due to coinductive projections.
2. **Termination of `sim-↾`:** Similar concern. The global type decreases through PR3/GR2 (peel msg) and PR7/GR3 (unfold mu), but Agda may not see this as structural.
3. **`merge-≤-branch` coinduction:** This is a coinductive proof (producing `≤` which is coinductive). Needs `--guardedness` and careful construction.
