# Formal MPST (Agda) - Syntax Guide

We represent labels and participants as finite sets. 
So the project is parameterised by `ℓ`, the number of labels, 
and `n`, the number of participants.

For this reason, most modules are of the form `ModuleName (ℓ n : _)`.

## Main Syntactic Domains (`SessionBase.agda`)

Each endpoint is modeled as a participant `p`.
- `Participant = Fin n`

Labels `l` are used to annotate choices and branches.
- `Label = Fin ℓ`

Payloads (`B ::= bool | nat | int`) represent the base sorts of communicated values.
- `Base` payload types:
  - `bool`
  - `nat`
  - `int`

## Operational Labels (`OperationalLabels.agda`)

An observable (`U ::= B | l`) is either a payload sort or a branch label. 
This essentially represents *something that can be communicated*. 
- `Observable`
  - `obsBase : Base → Observable`
  - `obsLabel : Label → Observable`

An action (`ζ ::= p!⟨U⟩ | p?⟨U⟩`) is either a local send or local receive. 
This is what one step looks like from the perspective of a given participant. 
- `Action`
  - `_!⟨_⟩ : Participant → Observable → Action`
  - `_?⟨_⟩ : Participant → Observable → Action`

A tagged action (`α ::= p ∶ ζ`) is much like an action, 
but it also records which participant performs the action.
- `TaggedAction`
  - `_∶_ : Participant → Action → TaggedAction`

An interaction (`ι ::= p ↝⟨U⟩ q`) is a synchronised communication from sender `p` to receiver `q`.
This is used in local context and global type semantics.
- `Interaction`
  - `_↝⟨_⟩_ : Participant → Observable → Participant → Interaction`

These are shared between local and global semantics.

## Local Session Type Syntax (`LocalSessionTypes.agda`)

The local syntax family is indexed by the number of recursion variables in scope:
- `Local : ℕ → Set`

At index `k`, the grammar is:

```text
T ::= end
    | send p B T
    | recv p B T
    | sel  p bs
    | bra  p bs
    | mu T
    | var i
```

Constructor signatures:
- `end  : Local k`
- `send : Participant → Base → Local k → Local k`
- `recv : Participant → Base → Local k → Local k`
- `sel  : Participant → Branches k → Local k`
- `bra  : Participant → Branches k → Local k`
- `mu   : Local (suc k) → Local k`
- `var  : Fin k → Local k`

### Well-scoped de Bruijn (local)

This *well-scoped de brujn* encoding makes scope correctness a typing invariant. This is slightly annoying 
but makes the proofs way easier.

Closed local types are exactly `Local₀ = Local 0` (because `Fin 0` has no inhabitants, 
so no free `var` can occur).

### Local branch tables and contexts

- `Branches k = Vec (Maybe (Local k)) ℓ`
- `lookupB : Label → Branches k → Maybe (Local k)`

Branching and selection use total finite tables over all labels, with `nothing`
for absent branches.

- `Δ = Participant → Local₀`
- `updateΔ : Participant → Local₀ → Δ → Δ`

## Global Session Type Syntax (`GlobalSessionTypes.agda`)

Global syntax is much the same as local syntax. 
The grammar is as follows:

```text
G ::= end
    | msg p q B G
    | choice p q bs
    | mu G
    | var i
```

Constructor signatures:
- `end    : Global k`
- `msg    : Participant → Participant → Base → Global k → Global k`
- `choice : Participant → Participant → Branches k → Global k`
- `mu     : Global (suc k) → Global k`
- `var    : Fin k → Global k`