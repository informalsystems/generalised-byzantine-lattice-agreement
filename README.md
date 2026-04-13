# generalised-byzantine-lattice-agreement

Quint specs for the Generalised Wait Till Safe (GWTS) algorithm from the paper
"Byzantine Generalized Lattice Agreement" (Di Luna, Anceaume, Querzoni, 2020).

The specs document two bugs in the `SAFE` predicate found during modelling, and
formally verify Bug 1 (the acceptor `AckReq` gate) using TLC temporal model
checking.

## Specs

### `gwts_lattice_agreement.qnt`

Full-fidelity Choreo-based spec of the GWTS protocol with the **correct** `SAFE`
predicates. Covers N=4, F=1, with both an all-correct instance (`gwts_standard`)
and a Byzantine instance (`gwts_byzantine`, one Byzantine node injecting values
outside the valid domain).

Use this spec for simulation and invariant checking:

```sh
# Simulate 200 steps and check safety invariants
quint run --invariant safety --main gwts_standard gwts_lattice_agreement.qnt

# Run the simulator against a specific invariant
quint run --invariant comparability \
          --main gwts_standard \
          --max-steps 500 \
          gwts_lattice_agreement.qnt
```

### `gwts_buggy_safe_alg4_tlc.qnt`

Minimal flat N=2 spec (no Choreo) with the **buggy** `SAFE_alg4` acceptor gate
(`∃r. proposed_set ⊆ svs[r]`). Designed for TLC exhaustive model checking of
Bug 1: from round 1 onwards, no acceptor can ever respond to an `AckReq` because
the cross-round `proposed_set = {1,2}` cannot fit inside any single `svs[r]`.

TLC finds a 27-step lasso counterexample in ~1.2 seconds (4238 distinct states).
No fairness assumption is needed, the block is structural.

```sh
# Find the lasso counterexample (should report a violation)
quint verify --temporal inclusivity_liveness_alg4 \
             gwts_buggy_safe_alg4_tlc.qnt --backend=tlc
```

### `gwts_correct_safe_alg4_tlc.qnt`

Same minimal flat N=2 spec but with the **correct** element-wise `SAFE` predicate
(`∀v ∈ proposed_set. ∃r. v ∈ svs[r]`). Confirms that the fix resolves the
liveness failure: TLC exhausts the full state space with no violation.

TLC checks 3381 distinct states in ~2 seconds and finds no violation.
Strong fairness is required to prevent spurious stutter counterexamples.

```sh
# Verify liveness holds with the correct SAFE (should report no violation)
quint verify --temporal inclusivity_liveness_alg4 \
             gwts_correct_safe_alg4_tlc.qnt --backend=tlc
```
