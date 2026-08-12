# First faithfulness review — worksheet

**Status: NOT REVIEWED.** Every verdict below is empty and may not be filled in
by an agent. `faithfulness` is the one human-only axis
(`.claude/decisions/ADR-0005-trust-axes.md:56`), and `faithfulness:
agent_drafted` was deliberately rejected there.

Regenerated from the real artifacts — `attest/lean-emission.json`,
`attest/declarations.json`, `registry/bridgeland2007.json`. Nothing here is
transcribed: `type_pp` is what the emitter measured, `statement_digest` is what
`mfc bundle` computed.

## What changed since the first draft

It listed **four** bindings. There are now **seven** — `mapEquiv_slicingDist`,
`actStabAut_slicingDist` and `AutPairQuot_smul_slicingDist` arrived with the
isometry work. That is exactly the regeneration the first draft warned would be
needed, and the reason it warned: `actStabAut` was claimed `one_way` *partly
because* the paper says `Aut(D)` acts by isometries and nothing here proved it.
**Re-read that claim first** — it may now be understated.

## The question, per entry

> Does the Lean declaration state what the paper's sentence says?

Not "does it typecheck". #51 cites TheoremGraph's statement-only experiment:
**22/24 typechecked, 5/24 were semantically faithful.** Typechecking is not
fidelity, and nothing mechanical separates them — which is why this axis is
human-only.

Answer `adequate` / `divergent` / `inadequate` / `inconclusive`. A `divergent`
or `inadequate` verdict **requires** at least one written divergence.

## Recording a verdict

Four of the five fields #51 asks for are below and stable. The fifth,
`reviewed_env_digest`, is **deliberately not baked in**: it changes with every
commit, so a value printed here would be stale by the time it was used. Produce
it at review time from the tree you reviewed against:

```sh
mfc env --repo . --out attest/environment.json \
        --axiom-allowlist propext,Quot.sound,Classical.choice \
        --emitter-version mfc-emit/1.0.0
```

`statement_digest` does **not** depend on the environment — it is a Merkle node
over `type_pp` and topic-local dependencies — so the values below stay valid
until the statement itself changes. That is what makes `statement_stable`
able to detect "same name, different statement".

---

## `CategoryTheory.Triangulated.mapEquiv_isLocallyFinite`

**cites** `bridgeland2007.def-5.7` — claimed **`no_claim`** (related, but no implication claimed)
**frontier:** none declared

**Author's note on the binding:**
> Bound to the locally-finite DEFINITION because this theorem is what preserves it, not what states it. no_claim is the honest relation: a transport result neither states the definition nor is implied by it.

### The paper says

> Definition 5.7. A slicing $\mathcal{P}$ of a triangulated category $\operatorname{\mathcal{D}}$ is locally-finite if there exists a real number $\eta>0$ such that for all $t\in\mathbb{R}$ the quasi-abelian category $\mathcal{P}((t-\eta,t+\eta))\subset\operatorname{\mathcal{D}}$ is of finite length. A stability condition $(Z,\mathcal{P})$ is locally-finite if the corresponding slicing $\mathcal{P}$ is.

### Lean says

```lean
∀ {C : Type u} [inst : CategoryTheory.Category.{w, u} C] [inst_1 : CategoryTheory.Limits.HasZeroObject.{w, u} C]
  [inst_2 : CategoryTheory.HasShift.{w, u, 0} C Int] [inst_3 : CategoryTheory.Preadditive.{w, u} C]
  [inst_4 : ∀ (n : Int), CategoryTheory.Functor.Additive.{w, u, w, u} (CategoryTheory.shiftFunctor.{w, u, 0} C n)]
  [inst_5 : CategoryTheory.Pretriangulated.{w, u} C] [inst_6 : CategoryTheory.IsTriangulated.{w, u} C]
  (Φ : CategoryTheory.Equivalence.{w, w, u, u} C C)
  [inst_7 : CategoryTheory.Functor.Additive.{w, u, w, u} (CategoryTheory.Equivalence.functor.{w, w, u, u} Φ)]
  [inst_8 : CategoryTheory.Functor.Additive.{w, u, w, u} (CategoryTheory.Equivalence.inverse.{w, w, u, u} Φ)]
  [inst_9 : CategoryTheory.Functor.CommShift.{w, u, w, u, 0} (CategoryTheory.Equivalence.functor.{w, w, u, u} Φ) Int]
  [inst_10 : CategoryTheory.Functor.CommShift.{w, u, w, u, 0} (CategoryTheory.Equivalence.inverse.{w, w, u, u} Φ) Int]
  [inst_11 : CategoryTheory.Functor.IsTriangulated.{w, u, w, u} (CategoryTheory.Equivalence.functor.{w, w, u, u} Φ)]
  [inst_12 : CategoryTheory.Functor.IsTriangulated.{w, u, w, u} (CategoryTheory.Equivalence.inverse.{w, w, u, u} Φ)]
  (s : CategoryTheory.Triangulated.Slicing.{w, u} C),
  CategoryTheory.Triangulated.Slicing.IsLocallyFinite.{w, u} C s →
    CategoryTheory.Triangulated.Slicing.IsLocallyFinite.{w, u} C
      (CategoryTheory.Triangulated.Slicing.mapEquiv.{w, u} s Φ)
```

### Digests to record

| field | value |
|---|---|
| `reviewed_statement_digest` | `a3d25e7d599cbe127927cc9143950a2618aa650b58136578b4780b63037d118f` |
| `reviewed_quote_sha256` | `829028bbb714a19f051deb50c8034eb77bda316b29f11f7811d0abecb4f9aa46` |
| `reviewed_env_digest` | *(run `mfc env` at review time)* |

### Verdict

| field | value |
|---|---|
| `faithfulness` | ☐ adequate ☐ divergent ☐ inadequate ☐ inconclusive |
| `relation_confirmed` | ☐ exact ☐ equivalent ☐ specialization ☐ one_way ☐ no_claim ☐ disputed |
| `divergences[]` | *(required if divergent/inadequate)* |
| `reviewer` / `reviewed_at` | |

**Is the claimed relation `no_claim` right?** It is a claim,
not a measurement, and confirming it is half of this review.

---

## `BridgelandStabLean.GroupAction.gltildeSlicingMulAction`

**cites** `bridgeland2007.lem-8.2` — claimed **`no_claim`** (related, but no implication claimed)
**frontier:** none declared

**Author's note on the binding:**
> A COMPONENT of the Lemma 8.2 action, not a weaker version of it: the paper states an action on Stab(D), and says nothing about GLTilde acting on slicings alone. Neither statement implies the other, so no_claim rather than one_way.

### The paper says

> Lemma 8.2. The generalised metric space $\operatorname{Stab}(\operatorname{\mathcal{D}})$ carries a right action of the group ${\tilde{\operatorname{GL^{+}}}}(2,\mathbb{R})$, the universal covering space of $\operatorname{GL^{+}}(2,\mathbb{R})$, and a left action by isometries of the group $\operatorname{Aut}(\operatorname{\mathcal{D}})$ of exact autoequivalences of $\operatorname{\mathcal{D}}$. These two actions commute.

### Lean says

```lean
(C : Type u) →
  [inst : CategoryTheory.Category.{v, u} C] →
    [inst_1 : CategoryTheory.Limits.HasZeroObject.{v, u} C] →
      [inst_2 : CategoryTheory.HasShift.{v, u, 0} C Int] →
        [inst_3 : CategoryTheory.Preadditive.{v, u} C] →
          [inst_4 :
              ∀ (n : Int), CategoryTheory.Functor.Additive.{v, u, v, u} (CategoryTheory.shiftFunctor.{v, u, 0} C n)] →
            [inst_5 : CategoryTheory.Pretriangulated.{v, u} C] →
              MulAction.{0, u} BridgelandStabLean.GroupAction.GLTilde (CategoryTheory.Triangulated.Slicing.{v, u} C)
```

### Digests to record

| field | value |
|---|---|
| `reviewed_statement_digest` | `143ae9c63258423e948c52b13c56b207c3769a16c30cbc97033c2ca49ee2ec9c` |
| `reviewed_quote_sha256` | `a82c3230040fd724ffad1d6655c190b00b99321d3fc1ab5eb74dafdfe8c38d1f` |
| `reviewed_env_digest` | *(run `mfc env` at review time)* |

### Verdict

| field | value |
|---|---|
| `faithfulness` | ☐ adequate ☐ divergent ☐ inadequate ☐ inconclusive |
| `relation_confirmed` | ☐ exact ☐ equivalent ☐ specialization ☐ one_way ☐ no_claim ☐ disputed |
| `divergences[]` | *(required if divergent/inadequate)* |
| `reviewer` / `reviewed_at` | |

**Is the claimed relation `no_claim` right?** It is a claim,
not a measurement, and confirming it is half of this review.

---

## `BridgelandStabLean.GroupAction.stabMulAction`

**cites** `bridgeland2007.lem-8.2` — claimed **`one_way`** (the cited statement implies this one, not conversely)
**frontier left open:** `gltilde-universal-cover`

**Author's note on the binding:**
> Lemma 8.2 names GLTilde as the universal covering space of GL+(2,R). Here it is a group of compatible pairs, proved to be a group and nothing more -- the covering-space facts are absent from Mathlib at this revision. The paper's statement implies this one; not conversely.

### The paper says

> Lemma 8.2. The generalised metric space $\operatorname{Stab}(\operatorname{\mathcal{D}})$ carries a right action of the group ${\tilde{\operatorname{GL^{+}}}}(2,\mathbb{R})$, the universal covering space of $\operatorname{GL^{+}}(2,\mathbb{R})$, and a left action by isometries of the group $\operatorname{Aut}(\operatorname{\mathcal{D}})$ of exact autoequivalences of $\operatorname{\mathcal{D}}$. These two actions commute.

### Lean says

```lean
(C : Type u) →
  [inst : CategoryTheory.Category.{w, u} C] →
    [inst_1 : CategoryTheory.Limits.HasZeroObject.{w, u} C] →
      [inst_2 : CategoryTheory.HasShift.{w, u, 0} C Int] →
        [inst_3 : CategoryTheory.Preadditive.{w, u} C] →
          [inst_4 :
              ∀ (n : Int), CategoryTheory.Functor.Additive.{w, u, w, u} (CategoryTheory.shiftFunctor.{w, u, 0} C n)] →
            [inst_5 : CategoryTheory.Pretriangulated.{w, u} C] →
              [inst_6 : CategoryTheory.IsTriangulated.{w, u} C] →
                {Λ : Type u'} →
                  [inst_7 : AddCommGroup.{u'} Λ] →
                    (v : AddMonoidHom.{u, u'} (CategoryTheory.Triangulated.K₀.{w, u} C) Λ) →
                      MulAction.{0, max u' u} BridgelandStabLean.GroupAction.GLTilde
                        (CategoryTheory.Triangulated.StabilityCondition.WithClassMap.{w, u, u'} C v)
```

### Digests to record

| field | value |
|---|---|
| `reviewed_statement_digest` | `7a5eac8743ad53491870e2b2ea9b843a580d3fb62ce0efe9144cd6ff70df1a6a` |
| `reviewed_quote_sha256` | `a82c3230040fd724ffad1d6655c190b00b99321d3fc1ab5eb74dafdfe8c38d1f` |
| `reviewed_env_digest` | *(run `mfc env` at review time)* |

### Verdict

| field | value |
|---|---|
| `faithfulness` | ☐ adequate ☐ divergent ☐ inadequate ☐ inconclusive |
| `relation_confirmed` | ☐ exact ☐ equivalent ☐ specialization ☐ one_way ☐ no_claim ☐ disputed |
| `divergences[]` | *(required if divergent/inadequate)* |
| `reviewer` / `reviewed_at` | |

**Is the claimed relation `one_way` right?** It is a claim,
not a measurement, and confirming it is half of this review.

---

## `CategoryTheory.Triangulated.AutPairQuot_smul_slicingDist`

**cites** `bridgeland2007.lem-8.2` — claimed **`no_claim`** (related, but no implication claimed)
**frontier:** none declared

**Author's note on the binding:**
> The closest this repo gets to 'Aut(D) acts by isometries', and still not it, for two independent reasons already recorded elsewhere in this repo. (1) The distance is slicingDist, not Bridgeland's d -- see mapEquiv_slicingDist's note; neither statement implies the other. (2) AutPairQuot v is NOT Aut(D): its elements are pairs (Phi, lam), and the forgetful map to AutQuot C is proved neither injective nor surjective. Cite this as 'the group of autoequivalences carrying a compatible class-lattice automorphism preserves the phase distance'.

### The paper says

> Lemma 8.2. The generalised metric space $\operatorname{Stab}(\operatorname{\mathcal{D}})$ carries a right action of the group ${\tilde{\operatorname{GL^{+}}}}(2,\mathbb{R})$, the universal covering space of $\operatorname{GL^{+}}(2,\mathbb{R})$, and a left action by isometries of the group $\operatorname{Aut}(\operatorname{\mathcal{D}})$ of exact autoequivalences of $\operatorname{\mathcal{D}}$. These two actions commute.

### Lean says

```lean
∀ {C : Type u} [inst : CategoryTheory.Category.{w, u} C] [inst_1 : CategoryTheory.Limits.HasZeroObject.{w, u} C]
  [inst_2 : CategoryTheory.HasShift.{w, u, 0} C Int] [inst_3 : CategoryTheory.Preadditive.{w, u} C]
  [inst_4 : ∀ (n : Int), CategoryTheory.Functor.Additive.{w, u, w, u} (CategoryTheory.shiftFunctor.{w, u, 0} C n)]
  [inst_5 : CategoryTheory.Pretriangulated.{w, u} C] [inst_6 : CategoryTheory.IsTriangulated.{w, u} C] {Λ : Type u'}
  [inst_7 : AddCommGroup.{u'} Λ] (v : AddMonoidHom.{u, u'} (CategoryTheory.Triangulated.K₀.{w, u} C) Λ)
  (g : BridgelandStabLean.GroupAction.AutPairQuot.{w, u, u'} v)
  (σ τ : CategoryTheory.Triangulated.StabilityCondition.WithClassMap.{w, u, u'} C v),
  Eq.{1}
    (CategoryTheory.Triangulated.slicingDist.{w, u} C
      (CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap.slicing.{w, u, u'}
        (CategoryTheory.Triangulated.StabilityCondition.WithClassMap.toWithClassMap.{w, u, u'}
          (HSMul.hSMul.{max (max u u') w, max u u', max u u'} g σ)))
      (CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap.slicing.{w, u, u'}
        (CategoryTheory.Triangulated.StabilityCondition.WithClassMap.toWithClassMap.{w, u, u'}
          (HSMul.hSMul.{max (max u u') w, max u u', max u u'} g τ))))
    (CategoryTheory.Triangulated.slicingDist.{w, u} C
      (CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap.slicing.{w, u, u'}
        (CategoryTheory.Triangulated.StabilityCondition.WithClassMap.toWithClassMap.{w, u, u'} σ))
      (CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap.slicing.{w, u, u'}
        (CategoryTheory.Triangulated.StabilityCondition.WithClassMap.toWithClassMap.{w, u, u'} τ)))
```

### Digests to record

| field | value |
|---|---|
| `reviewed_statement_digest` | `988e500e57c6d661dab7706b34b28f9d742f9a08c3d73d213e1b41cbde7008b4` |
| `reviewed_quote_sha256` | `a82c3230040fd724ffad1d6655c190b00b99321d3fc1ab5eb74dafdfe8c38d1f` |
| `reviewed_env_digest` | *(run `mfc env` at review time)* |

### Verdict

| field | value |
|---|---|
| `faithfulness` | ☐ adequate ☐ divergent ☐ inadequate ☐ inconclusive |
| `relation_confirmed` | ☐ exact ☐ equivalent ☐ specialization ☐ one_way ☐ no_claim ☐ disputed |
| `divergences[]` | *(required if divergent/inadequate)* |
| `reviewer` / `reviewed_at` | |

**Is the claimed relation `no_claim` right?** It is a claim,
not a measurement, and confirming it is half of this review.

---

## `CategoryTheory.Triangulated.actStabAut`

**cites** `bridgeland2007.lem-8.2` — claimed **`one_way`** (the cited statement implies this one, not conversely)
**frontier:** none declared

**Author's note on the binding:**
> The Aut half of Lemma 8.2, and weaker than it in two stated ways. The paper says Aut(D) acts by ISOMETRIES; that clause is not proved. What IS proved is actStabAut_slicingDist (AutIsometry.lean): this map preserves the anchor's slicingDist, which carries the two phase discrepancies of Bridgeland's d and omits the mass ratio |log(m2/m1)|. That omission is not closable at this pin -- the anchor defines no mass function. And the acting object is a PAIR (Phi, lam) rather than an autoequivalence, so this is not a MulAction -- AutQuot groups the Phi's alone, which suffices for slicings but not once a class lattice is in play.

### The paper says

> Lemma 8.2. The generalised metric space $\operatorname{Stab}(\operatorname{\mathcal{D}})$ carries a right action of the group ${\tilde{\operatorname{GL^{+}}}}(2,\mathbb{R})$, the universal covering space of $\operatorname{GL^{+}}(2,\mathbb{R})$, and a left action by isometries of the group $\operatorname{Aut}(\operatorname{\mathcal{D}})$ of exact autoequivalences of $\operatorname{\mathcal{D}}$. These two actions commute.

### Lean says

```lean
{C : Type u} →
  [inst : CategoryTheory.Category.{w, u} C] →
    [inst_1 : CategoryTheory.Limits.HasZeroObject.{w, u} C] →
      [inst_2 : CategoryTheory.HasShift.{w, u, 0} C Int] →
        [inst_3 : CategoryTheory.Preadditive.{w, u} C] →
          [inst_4 :
              ∀ (n : Int), CategoryTheory.Functor.Additive.{w, u, w, u} (CategoryTheory.shiftFunctor.{w, u, 0} C n)] →
            [inst_5 : CategoryTheory.Pretriangulated.{w, u} C] →
              [inst_6 : CategoryTheory.IsTriangulated.{w, u} C] →
                (Φ : CategoryTheory.Equivalence.{w, w, u, u} C C) →
                  [CategoryTheory.Functor.Additive.{w, u, w, u} (CategoryTheory.Equivalence.functor.{w, w, u, u} Φ)] →
                    [inst_8 :
                        CategoryTheory.Functor.Additive.{w, u, w, u}
                          (CategoryTheory.Equivalence.inverse.{w, w, u, u} Φ)] →
                      [inst_9 :
                          CategoryTheory.Functor.CommShift.{w, u, w, u, 0}
                            (CategoryTheory.Equivalence.functor.{w, w, u, u} Φ) Int] →
                        [inst_10 :
                            CategoryTheory.Functor.CommShift.{w, u, w, u, 0}
                              (CategoryTheory.Equivalence.inverse.{w, w, u, u} Φ) Int] →
                          [CategoryTheory.Functor.IsTriangulated.{w, u, w, u}
                                (CategoryTheory.Equivalence.functor.{w, w, u, u} Φ)] →
                            [inst_12 :
                                CategoryTheory.Functor.IsTriangulated.{w, u, w, u}
                                  (CategoryTheory.Equivalence.inverse.{w, w, u, u} Φ)] →
                              {Λ : Type u'} →
                                [inst_13 : AddCommGroup.{u'} Λ] →
                                  (v : AddMonoidHom.{u, u'} (CategoryTheory.Triangulated.K₀.{w, u} C) Λ) →
                                    (lam : AddMonoidHom.{u', u'} Λ Λ) →
                                      (∀ (x : CategoryTheory.Triangulated.K₀.{w, u} C),
                                          Eq.{u' + 1}
                                            (v
                                              ((CategoryTheory.Triangulated.K₀.mapF.{w, u}
                                                  (CategoryTheory.Equivalence.inverse.{w, w, u, u} Φ))
                                                x))
                                            (lam (v x))) →
                                        CategoryTheory.Triangulated.StabilityCondition.WithClassMap.{w, u, u'} C v →
                                          CategoryTheory.Triangulated.StabilityCondition.WithClassMap.{w, u, u'} C v
```

### Digests to record

| field | value |
|---|---|
| `reviewed_statement_digest` | `e4d725ce4bab744d9faaf1890f1a0943f076ed74aa612736d88fdb62f432aec4` |
| `reviewed_quote_sha256` | `a82c3230040fd724ffad1d6655c190b00b99321d3fc1ab5eb74dafdfe8c38d1f` |
| `reviewed_env_digest` | *(run `mfc env` at review time)* |

### Verdict

| field | value |
|---|---|
| `faithfulness` | ☐ adequate ☐ divergent ☐ inadequate ☐ inconclusive |
| `relation_confirmed` | ☐ exact ☐ equivalent ☐ specialization ☐ one_way ☐ no_claim ☐ disputed |
| `divergences[]` | *(required if divergent/inadequate)* |
| `reviewer` / `reviewed_at` | |

**Is the claimed relation `one_way` right?** It is a claim,
not a measurement, and confirming it is half of this review.

---

## `CategoryTheory.Triangulated.actStabAut_slicingDist`

**cites** `bridgeland2007.lem-8.2` — claimed **`no_claim`** (related, but no implication claimed)
**frontier:** none declared

**Author's note on the binding:**
> Same non-implication as mapEquiv_slicingDist: the distance is the anchor's slicingDist, not Bridgeland's d, and d omits nothing while slicingDist omits the mass ratio. What this adds over that theorem is only the carrier -- the statement is now about stability conditions rather than bare slicings, matching the paper's Stab(D). It is still not the paper's isometry claim.

### The paper says

> Lemma 8.2. The generalised metric space $\operatorname{Stab}(\operatorname{\mathcal{D}})$ carries a right action of the group ${\tilde{\operatorname{GL^{+}}}}(2,\mathbb{R})$, the universal covering space of $\operatorname{GL^{+}}(2,\mathbb{R})$, and a left action by isometries of the group $\operatorname{Aut}(\operatorname{\mathcal{D}})$ of exact autoequivalences of $\operatorname{\mathcal{D}}$. These two actions commute.

### Lean says

```lean
∀ {C : Type u} [inst : CategoryTheory.Category.{w, u} C] [inst_1 : CategoryTheory.Limits.HasZeroObject.{w, u} C]
  [inst_2 : CategoryTheory.HasShift.{w, u, 0} C Int] [inst_3 : CategoryTheory.Preadditive.{w, u} C]
  [inst_4 : ∀ (n : Int), CategoryTheory.Functor.Additive.{w, u, w, u} (CategoryTheory.shiftFunctor.{w, u, 0} C n)]
  [inst_5 : CategoryTheory.Pretriangulated.{w, u} C] [inst_6 : CategoryTheory.IsTriangulated.{w, u} C]
  (Φ : CategoryTheory.Equivalence.{w, w, u, u} C C)
  [inst_7 : CategoryTheory.Functor.Additive.{w, u, w, u} (CategoryTheory.Equivalence.functor.{w, w, u, u} Φ)]
  [inst_8 : CategoryTheory.Functor.Additive.{w, u, w, u} (CategoryTheory.Equivalence.inverse.{w, w, u, u} Φ)]
  [inst_9 : CategoryTheory.Functor.CommShift.{w, u, w, u, 0} (CategoryTheory.Equivalence.functor.{w, w, u, u} Φ) Int]
  [inst_10 : CategoryTheory.Functor.CommShift.{w, u, w, u, 0} (CategoryTheory.Equivalence.inverse.{w, w, u, u} Φ) Int]
  [inst_11 : CategoryTheory.Functor.IsTriangulated.{w, u, w, u} (CategoryTheory.Equivalence.functor.{w, w, u, u} Φ)]
  [inst_12 : CategoryTheory.Functor.IsTriangulated.{w, u, w, u} (CategoryTheory.Equivalence.inverse.{w, w, u, u} Φ)]
  {Λ : Type u'} [inst_13 : AddCommGroup.{u'} Λ] (v : AddMonoidHom.{u, u'} (CategoryTheory.Triangulated.K₀.{w, u} C) Λ)
  (lam : AddMonoidHom.{u', u'} Λ Λ)
  (hlam :
    ∀ (x : CategoryTheory.Triangulated.K₀.{w, u} C),
      Eq.{u' + 1}
        (v ((CategoryTheory.Triangulated.K₀.mapF.{w, u} (CategoryTheory.Equivalence.inverse.{w, w, u, u} Φ)) x))
        (lam (v x)))
  (σ τ : CategoryTheory.Triangulated.StabilityCondition.WithClassMap.{w, u, u'} C v),
  Eq.{1}
    (CategoryTheory.Triangulated.slicingDist.{w, u} C
      (CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap.slicing.{w, u, u'}
        (CategoryTheory.Triangulated.StabilityCondition.WithClassMap.toWithClassMap.{w, u, u'}
          (CategoryTheory.Triangulated.actStabAut.{w, u, u'} Φ v lam hlam σ)))
      (CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap.slicing.{w, u, u'}
        (CategoryTheory.Triangulated.StabilityCondition.WithClassMap.toWithClassMap.{w, u, u'}
          (CategoryTheory.Triangulated.actStabAut.{w, u, u'} Φ v lam hlam τ))))
    (CategoryTheory.Triangulated.slicingDist.{w, u} C
      (CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap.slicing.{w, u, u'}
        (CategoryTheory.Triangulated.StabilityCondition.WithClassMap.toWithClassMap.{w, u, u'} σ))
      (CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap.slicing.{w, u, u'}
        (CategoryTheory.Triangulated.StabilityCondition.WithClassMap.toWithClassMap.{w, u, u'} τ)))
```

### Digests to record

| field | value |
|---|---|
| `reviewed_statement_digest` | `a768232d7e9bbfd871f439ec81103c4d7b691e9b3b9d35aec667dbcd85068afe` |
| `reviewed_quote_sha256` | `a82c3230040fd724ffad1d6655c190b00b99321d3fc1ab5eb74dafdfe8c38d1f` |
| `reviewed_env_digest` | *(run `mfc env` at review time)* |

### Verdict

| field | value |
|---|---|
| `faithfulness` | ☐ adequate ☐ divergent ☐ inadequate ☐ inconclusive |
| `relation_confirmed` | ☐ exact ☐ equivalent ☐ specialization ☐ one_way ☐ no_claim ☐ disputed |
| `divergences[]` | *(required if divergent/inadequate)* |
| `reviewer` / `reviewed_at` | |

**Is the claimed relation `no_claim` right?** It is a claim,
not a measurement, and confirming it is half of this review.

---

## `CategoryTheory.Triangulated.mapEquiv_slicingDist`

**cites** `bridgeland2007.lem-8.2` — claimed **`no_claim`** (related, but no implication claimed)
**frontier:** none declared

**Author's note on the binding:**
> The ISOMETRY clause of Lemma 8.2, for a DIFFERENT distance, so neither statement implies the other. The paper's d is a sup of THREE quantities; the anchor's slicingDist carries the two phase discrepancies and omits |log(m2/m1)|, the mass ratio -- the only term that sees the central charge, hence the only one Z-composed-with-lam could move. A sup of three being preserved does not give that each term is, so isometry for d does NOT imply this; and preserving slicingDist plainly does not imply isometry for d. Separately, slicingDist is a distance on Slicing C, not on Stab(D). The anchor defines no mass function, so the omitted term is not expressible at this pin.

### The paper says

> Lemma 8.2. The generalised metric space $\operatorname{Stab}(\operatorname{\mathcal{D}})$ carries a right action of the group ${\tilde{\operatorname{GL^{+}}}}(2,\mathbb{R})$, the universal covering space of $\operatorname{GL^{+}}(2,\mathbb{R})$, and a left action by isometries of the group $\operatorname{Aut}(\operatorname{\mathcal{D}})$ of exact autoequivalences of $\operatorname{\mathcal{D}}$. These two actions commute.

### Lean says

```lean
∀ {C : Type u} [inst : CategoryTheory.Category.{w, u} C] [inst_1 : CategoryTheory.Limits.HasZeroObject.{w, u} C]
  [inst_2 : CategoryTheory.HasShift.{w, u, 0} C Int] [inst_3 : CategoryTheory.Preadditive.{w, u} C]
  [inst_4 : ∀ (n : Int), CategoryTheory.Functor.Additive.{w, u, w, u} (CategoryTheory.shiftFunctor.{w, u, 0} C n)]
  [inst_5 : CategoryTheory.Pretriangulated.{w, u} C] (Φ : CategoryTheory.Equivalence.{w, w, u, u} C C)
  [inst_6 : CategoryTheory.Functor.Additive.{w, u, w, u} (CategoryTheory.Equivalence.functor.{w, w, u, u} Φ)]
  [inst_7 : CategoryTheory.Functor.Additive.{w, u, w, u} (CategoryTheory.Equivalence.inverse.{w, w, u, u} Φ)]
  [inst_8 : CategoryTheory.Functor.CommShift.{w, u, w, u, 0} (CategoryTheory.Equivalence.functor.{w, w, u, u} Φ) Int]
  [inst_9 : CategoryTheory.Functor.CommShift.{w, u, w, u, 0} (CategoryTheory.Equivalence.inverse.{w, w, u, u} Φ) Int]
  [inst_10 : CategoryTheory.Functor.IsTriangulated.{w, u, w, u} (CategoryTheory.Equivalence.functor.{w, w, u, u} Φ)]
  [inst_11 : CategoryTheory.Functor.IsTriangulated.{w, u, w, u} (CategoryTheory.Equivalence.inverse.{w, w, u, u} Φ)]
  (s₁ s₂ : CategoryTheory.Triangulated.Slicing.{w, u} C),
  Eq.{1}
    (CategoryTheory.Triangulated.slicingDist.{w, u} C (CategoryTheory.Triangulated.Slicing.mapEquiv.{w, u} s₁ Φ)
      (CategoryTheory.Triangulated.Slicing.mapEquiv.{w, u} s₂ Φ))
    (CategoryTheory.Triangulated.slicingDist.{w, u} C s₁ s₂)
```

### Digests to record

| field | value |
|---|---|
| `reviewed_statement_digest` | `cc7028040d0317d8a517416a5def9e05a84b037f918bf6a0ec432d53f67b2170` |
| `reviewed_quote_sha256` | `a82c3230040fd724ffad1d6655c190b00b99321d3fc1ab5eb74dafdfe8c38d1f` |
| `reviewed_env_digest` | *(run `mfc env` at review time)* |

### Verdict

| field | value |
|---|---|
| `faithfulness` | ☐ adequate ☐ divergent ☐ inadequate ☐ inconclusive |
| `relation_confirmed` | ☐ exact ☐ equivalent ☐ specialization ☐ one_way ☐ no_claim ☐ disputed |
| `divergences[]` | *(required if divergent/inadequate)* |
| `reviewer` / `reviewed_at` | |

**Is the claimed relation `no_claim` right?** It is a claim,
not a measurement, and confirming it is half of this review.

---

## Coverage, stated rather than implied

7 bindings over 2 registry keys, against
310 in-scope declarations in this repo and 8 registry
entries drawn from a notebook of 146 papers / 15,280 chunks.

Reviewing these makes `human_review` non-`none` **for these entries only**. A
repo-level `human_review` reading anything else while that is true is the
collapse ADR-0005 forbids.
