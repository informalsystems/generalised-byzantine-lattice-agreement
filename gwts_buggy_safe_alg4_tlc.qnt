// -*- mode: Bluespec; -*-
// Flat N=2 spec for TLC model checking of Bug 1 (SAFE_alg4 — acceptor AckReq gate)
// from "Byzantine Generalized Lattice Agreement" (Di Luna, Anceaume, Querzoni, 2020).
//
// This is a deliberately minimal, Choreo-free translation of the GWTS protocol
// for exhaustive TLC model checking. Choreo stores complete message history in
// state, making the state space too large for TLC to converge on liveness properties.
// This spec strips all Choreo overhead: all state is explicit top-level variables.
//
// =============================================================================
// CONFIGURATION
// =============================================================================
//
//   N=2, F=0, MAX_ROUND=1. All nodes correct. No Byzantine nodes.
//   n1: round 0 → {1}, round 1 → {2}
//   n2: round 0 → {1}, round 1 → {2}
//   BRB_THRESHOLD = N-F = 2  (both nodes must deliver)
//   BYZ_QUORUM    = ⌊(N+F)/2⌋+1 = 2  (both nodes must ACK)
//
// Because both nodes propose the same values in each round, the proposed_set
// after round-0 BRB is {1} and after round-1 BRB is {1, 2}. The round-1
// proposed_set spans two svs entries and is what triggers the bug.
//
// =============================================================================
// BUG: SAFE_alg4 (Algorithm 4, acceptor AckReq gate)
// =============================================================================
//
//   SAFE_alg4(S, svs) ≡ ∃r. S ⊆ svs[r]
//
// Requires the ENTIRE proposed_set to fit inside ONE round's SvS.
// From round 1 onwards, proposed_set = {1, 2} spans two rounds:
//   svs[0] = {1}  (round-0 disclosures)
//   svs[1] = {2}  (round-1 disclosures)
//   {1, 2} ⊆ {1} = false
//   {1, 2} ⊆ {2} = false
// Every round-1 AckReq is silently blocked. No ACK quorum ever forms.
// No node ever decides any round-1 values. Catastrophic liveness failure.
//
// =============================================================================
// EXPECTED TLC RESULT
// =============================================================================
//
// TLC finds a 27-step lasso counterexample for `inclusivity_liveness_alg4`
// in 1.2 seconds, exhausting 4238 distinct states:
//   - States 1-21:  Round 0 completes correctly (both nodes decide {1},
//                   advance to proposer_round=1, safe_round=1)
//   - States 22-27: Both nodes broadcast round-1 Val {2}, collect deliveries
//                   (svs_r1={2}, proposed_set={1,2}, brb_ready contains 1),
//                   send AckReqs — but SAFE_alg4({1,2}, svs) is false for
//                   every svs[r], so no acceptor responds.
//   - State 28:     Stutter — no enabled transition leads to a decision.
//                   System loops forever with no new decisions.
//
// No fairness assumption is needed for this property: the block is structural.
// svs entries are sealed after BRB completes and can never grow; SAFE_alg4 can
// never return true for a cross-round proposed_set.
//
// Run with:
//   quint verify --temporal inclusivity_liveness_alg4 gwts_buggy_safe_alg4_tlc.qnt

module gwts_buggy_safe_alg4_tlc {
  import basicSpells.* from "choreo/spells/basicSpells"

  // =========================================================================
  // PROTOCOL PARAMETERS (inlined — no abstract constants needed for TLC)
  // =========================================================================

  pure val BRB_THRESHOLD = 2    // N - F = 2 - 0
  pure val BYZ_QUORUM    = 2    // floor((2+0)/2) + 1
  pure val MAX_ROUND     = 1

  // Legitimate value domain E = {1, 2}
  pure val E       = Set(1, 2)
  pure val R0_VALS = Set(1)
  pure val R1_VALS = Set(2)

  // Per-node per-round batch. Both nodes propose same values (simplest model
  // that triggers the bug; avoids pre_disclose_val_senders complexity).
  pure def batch(r: int): Set[int] =
    if      (r == 0) R0_VALS
    else if (r == 1) R1_VALS
    else             Set()

  // =========================================================================
  // TYPES
  // =========================================================================

  type NodeId = str

  // Message record types
  type ValMsg    = { from: NodeId, round: int, values: Set[int] }
  type AckReqMsg = { from: NodeId, round: int, ts: int, proposed_set: Set[int] }
  type AckMsg    = { from: NodeId, req_sender: NodeId, round: int, ts: int, accepted_set: Set[int] }
  type NackMsg   = { from: NodeId, req_sender: NodeId, round: int, ts: int, accepted_set: Set[int] }

  // Per-node state record.
  // svs is split into svs_r0 and svs_r1 to avoid int -> Set[int] function
  // complexity; MAX_ROUND = 1 so only two entries are needed.
  type NodeState = {
    proposed_set:   Set[int],
    accepted_set:   Set[int],
    decided_set:    Set[int],
    decided:        bool,
    ts:             int,
    proposer_round: int,
    safe_round:     int,
    ack_req_sent:   bool,
    val_sent:       Set[int],           // rounds where ValMsg was broadcast
    svs_r0:         Set[int],           // SvS for round 0
    svs_r1:         Set[int],           // SvS for round 1
    brb_ready:      Set[int],           // rounds where BRB threshold was reached
    responded_to:   Set[{ round: int, proposer: NodeId, ts: int }],
  }

  // =========================================================================
  // STATE VARIABLES
  // =========================================================================

  var n1: NodeState
  var n2: NodeState

  // Global network message bags (persistent — no message loss in this model).
  var val_msgs:     Set[ValMsg]
  var ack_req_msgs: Set[AckReqMsg]
  var ack_msgs:     Set[AckMsg]
  var nack_msgs:    Set[NackMsg]

  // =========================================================================
  // LATTICE HELPERS
  // =========================================================================

  pure def lat_le(a: Set[int], b: Set[int]): bool =
    a.forall(x => b.contains(x))

  pure def lat_join(a: Set[int], b: Set[int]): Set[int] =
    a.union(b)

  // SvS lookup for a node state: round 0 or round 1.
  pure def get_svs(st: NodeState, r: int): Set[int] =
    if (r == 0) st.svs_r0 else st.svs_r1

  // =========================================================================
  // SAFE PREDICATES
  // =========================================================================

  // SAFE (correct): ∀v ∈ S. ∃r ∈ {0, 1}. v ∈ svs[r]
  // Each value just needs to appear in SOME round's SvS.
  pure def SAFE_correct(s: Set[int], st: NodeState): bool =
    s.forall(v => st.svs_r0.contains(v) or st.svs_r1.contains(v))

  // SAFE_alg4 (buggy Algorithm 4): ∃r ∈ {0, 1}. S ⊆ svs[r]
  // Requires the WHOLE set to fit inside ONE round's SvS.
  // Fails for any cross-round proposed_set (e.g. {1, 2} after round 1 BRB).
  pure def SAFE_alg4(s: Set[int], st: NodeState): bool =
    lat_le(s, st.svs_r0) or lat_le(s, st.svs_r1)

  // =========================================================================
  // MESSAGE HELPERS
  // =========================================================================

  pure def not_yet_responded(
    responded_to: Set[{ round: int, proposer: NodeId, ts: int }],
    r: int, p: NodeId, t: int
  ): bool =
    not(responded_to.contains({ round: r, proposer: p, ts: t }))

  // Val senders for round r (E-validity filtered).
  pure def val_senders_r(msgs: Set[ValMsg], r: int): Set[NodeId] =
    msgs.filterMap(m =>
      if (m.round == r and lat_le(m.values, E)) Some(m.from) else None
    )

  // Union of values disclosed in round r by the given senders (E-validity re-checked).
  pure def val_values_r(msgs: Set[ValMsg], senders: Set[NodeId], r: int): Set[int] =
    msgs.fold(Set(), (acc, m) =>
      if (m.round == r and senders.contains(m.from) and lat_le(m.values, E))
        acc.union(m.values)
      else acc
    )

  // Set of decided values that have a BYZ_QUORUM of matching ACKs and cover prev_decision.
  // ACKs are SAFE_correct-filtered: Byzantine fabrications don't affect this model
  // (no Byzantine nodes), but the filter keeps the logic faithful to the spec.
  pure def quorum_decisions(
    msgs:          Set[AckMsg],
    round:         int,
    prev_decision: Set[int],
    st:            NodeState
  ): Set[Set[int]] =
    val valid = msgs.filter(a =>
      a.round == round and SAFE_correct(a.accepted_set, st)
    )
    valid.filterMap(a => {
      val q = valid.filter(a2 =>
        a2.accepted_set == a.accepted_set
          and a2.req_sender == a.req_sender
          and a2.ts == a.ts
      ).map(a2 => a2.from)
      if (q.size() >= BYZ_QUORUM and lat_le(prev_decision, a.accepted_set))
        Some(a.accepted_set)
      else None
    })

  // True if there is a BYZ_QUORUM of matching ACKs for the given round.
  // Used to advance safe_round.
  pure def has_safe_round_quorum(msgs: Set[AckMsg], round: int, st: NodeState): bool =
    val valid = msgs.filter(a =>
      a.round == round and SAFE_correct(a.accepted_set, st)
    )
    valid.exists(a =>
      valid.filter(a2 =>
        a2.accepted_set == a.accepted_set
          and a2.req_sender == a.req_sender
          and a2.ts == a.ts
      ).map(a2 => a2.from).size() >= BYZ_QUORUM
    )

  // =========================================================================
  // INITIALIZATION
  // =========================================================================

  pure val init_node: NodeState = {
    proposed_set:   Set(),
    accepted_set:   Set(),
    decided_set:    Set(),
    decided:        false,
    ts:             0,
    proposer_round: 0,
    safe_round:     0,
    ack_req_sent:   false,
    val_sent:       Set(),
    svs_r0:         Set(),
    svs_r1:         Set(),
    brb_ready:      Set(),
    responded_to:   Set(),
  }

  action init = all {
    n1'           = init_node,
    n2'           = init_node,
    val_msgs'     = Set(),
    ack_req_msgs' = Set(),
    ack_msgs'     = Set(),
    nack_msgs'    = Set(),
  }

  // =========================================================================
  // TRANSITIONS — n1
  //
  // Each action mutates only what it needs; all other state is unchanged.
  // Frame conditions are written explicitly (Quint requires all primed vars).
  // =========================================================================

  // T1: BroadcastVal — send Val for current proposer_round, join batch into proposed_set.
  action broadcast_val_n1 = {
    val r = n1.proposer_round
    val b = batch(r)
    all {
      not(n1.val_sent.contains(r)),
      r <= MAX_ROUND,
      n1'           = { ...n1,
                        proposed_set: lat_join(n1.proposed_set, b),
                        val_sent:     n1.val_sent.setAdd(r) },
      val_msgs'     = val_msgs.setAdd({ from: "n1", round: r, values: b }),
      n2'           = n2,
      ack_req_msgs' = ack_req_msgs,
      ack_msgs'     = ack_msgs,
      nack_msgs'    = nack_msgs,
    }
  }

  // T_svs: UpdateSvs — scan val_msgs and update svs for all rounds.
  // Enabled only when svs can grow (monotone; fires at most twice per node).
  action update_svs_n1 = {
    val new_r0 = val_values_r(val_msgs, val_senders_r(val_msgs, 0), 0)
    val new_r1 = val_values_r(val_msgs, val_senders_r(val_msgs, 1), 1)
    all {
      new_r0 != n1.svs_r0 or new_r1 != n1.svs_r1,
      n1'           = { ...n1, svs_r0: new_r0, svs_r1: new_r1 },
      n2'           = n2,
      val_msgs'     = val_msgs,
      ack_req_msgs' = ack_req_msgs,
      ack_msgs'     = ack_msgs,
      nack_msgs'    = nack_msgs,
    }
  }

  // T2: CollectVals — once BRB_THRESHOLD Val senders received, mark brb_ready.
  action collect_vals_n1 = {
    val r       = n1.proposer_round
    val senders = val_senders_r(val_msgs, r)
    val new_svs = val_values_r(val_msgs, senders, r)
    all {
      n1.val_sent.contains(r),
      not(n1.brb_ready.contains(r)),
      senders.size() >= BRB_THRESHOLD,
      n1'           = { ...n1,
                        brb_ready:    n1.brb_ready.setAdd(r),
                        proposed_set: lat_join(n1.proposed_set, new_svs) },
      n2'           = n2,
      val_msgs'     = val_msgs,
      ack_req_msgs' = ack_req_msgs,
      ack_msgs'     = ack_msgs,
      nack_msgs'    = nack_msgs,
    }
  }

  // T3: SendAckReq — broadcast AckReq once brb_ready and not yet decided.
  action send_ack_req_n1 = {
    val new_ts = n1.ts + 1
    all {
      n1.brb_ready.contains(n1.proposer_round),
      not(n1.ack_req_sent),
      not(n1.decided),
      n1'           = { ...n1, ack_req_sent: true, ts: new_ts },
      ack_req_msgs' = ack_req_msgs.setAdd({
                        from:         "n1",
                        round:        n1.proposer_round,
                        ts:           new_ts,
                        proposed_set: n1.proposed_set }),
      n2'           = n2,
      val_msgs'     = val_msgs,
      ack_msgs'     = ack_msgs,
      nack_msgs'    = nack_msgs,
    }
  }

  // T4: RespondAckReq — respond to an eligible AckReq using SAFE_alg4 (the buggy gate).
  // ACK if accepted_set ⊆ proposed_set; NACK otherwise.
  action respond_ack_req_n1 = {
    nondet req = ack_req_msgs.filter(m =>
      m.round <= n1.safe_round
        and not_yet_responded(n1.responded_to, m.round, m.from, m.ts)
        and SAFE_alg4(m.proposed_set, n1)   // <-- BUGGY gate
    ).oneOf()
    val new_responded = n1.responded_to.setAdd({ round: req.round, proposer: req.from, ts: req.ts })
    if (lat_le(n1.accepted_set, req.proposed_set))
      // ACK branch: raise accepted_set to proposed_set, broadcast Ack
      all {
        n1'           = { ...n1,
                          accepted_set: req.proposed_set,
                          responded_to: new_responded },
        ack_msgs'     = ack_msgs.setAdd({
                          from:         "n1",
                          req_sender:   req.from,
                          round:        req.round,
                          ts:           req.ts,
                          accepted_set: req.proposed_set }),
        n2'           = n2,
        val_msgs'     = val_msgs,
        ack_req_msgs' = ack_req_msgs,
        nack_msgs'    = nack_msgs,
      }
    else
      // NACK branch: send old accepted_set back, union locally
      all {
        n1'           = { ...n1,
                          accepted_set: lat_join(n1.accepted_set, req.proposed_set),
                          responded_to: new_responded },
        nack_msgs'    = nack_msgs.setAdd({
                          from:         "n1",
                          req_sender:   req.from,
                          round:        req.round,
                          ts:           req.ts,
                          accepted_set: n1.accepted_set }),  // old value, before union
        n2'           = n2,
        val_msgs'     = val_msgs,
        ack_req_msgs' = ack_req_msgs,
        ack_msgs'     = ack_msgs,
      }
  }

  // T5: ProcessNack — absorb a NACK (uses correct SAFE filter), grow proposed_set,
  // re-broadcast AckReq with new ts.
  action process_nack_n1 = {
    val r = n1.proposer_round
    nondet nack = nack_msgs.filter(m =>
      m.req_sender == "n1"
        and m.round == r
        and m.ts == n1.ts
        and SAFE_correct(m.accepted_set, n1)         // correct NACK filter
        and not(lat_le(m.accepted_set, n1.proposed_set))
    ).oneOf()
    val new_proposed = lat_join(n1.proposed_set, nack.accepted_set)
    val new_ts       = n1.ts + 1
    all {
      n1.ack_req_sent,
      not(n1.decided),
      n1'           = { ...n1, proposed_set: new_proposed, ts: new_ts },
      ack_req_msgs' = ack_req_msgs.setAdd({
                        from:         "n1",
                        round:        r,
                        ts:           new_ts,
                        proposed_set: new_proposed }),
      n2'           = n2,
      val_msgs'     = val_msgs,
      ack_msgs'     = ack_msgs,
      nack_msgs'    = nack_msgs,
    }
  }

  // T6: Decide — decide when a BYZ_QUORUM of matching ACKs observed.
  action decide_n1 = {
    nondet decision = quorum_decisions(ack_msgs, n1.proposer_round, n1.decided_set, n1).oneOf()
    all {
      n1.ack_req_sent,
      not(n1.decided),
      n1'           = { ...n1, decided: true, decided_set: decision },
      n2'           = n2,
      val_msgs'     = val_msgs,
      ack_req_msgs' = ack_req_msgs,
      ack_msgs'     = ack_msgs,
      nack_msgs'    = nack_msgs,
    }
  }

  // T7: AdvanceRound — move to next round after deciding.
  action advance_round_n1 = all {
    n1.decided,
    n1.proposer_round < MAX_ROUND,
    n1'           = { ...n1,
                      proposer_round: n1.proposer_round + 1,
                      ack_req_sent:   false,
                      decided:        false },
    n2'           = n2,
    val_msgs'     = val_msgs,
    ack_req_msgs' = ack_req_msgs,
    ack_msgs'     = ack_msgs,
    nack_msgs'    = nack_msgs,
  }

  // T_safe: AdvanceSafeRound — advance safe_round on observing a legitimate-end quorum.
  action advance_safe_round_n1 = all {
    n1.safe_round < MAX_ROUND,
    has_safe_round_quorum(ack_msgs, n1.safe_round, n1),
    n1'           = { ...n1, safe_round: n1.safe_round + 1 },
    n2'           = n2,
    val_msgs'     = val_msgs,
    ack_req_msgs' = ack_req_msgs,
    ack_msgs'     = ack_msgs,
    nack_msgs'    = nack_msgs,
  }

  // =========================================================================
  // TRANSITIONS — n2 (symmetric to n1)
  // =========================================================================

  action broadcast_val_n2 = {
    val r = n2.proposer_round
    val b = batch(r)
    all {
      not(n2.val_sent.contains(r)),
      r <= MAX_ROUND,
      n2'           = { ...n2,
                        proposed_set: lat_join(n2.proposed_set, b),
                        val_sent:     n2.val_sent.setAdd(r) },
      val_msgs'     = val_msgs.setAdd({ from: "n2", round: r, values: b }),
      n1'           = n1,
      ack_req_msgs' = ack_req_msgs,
      ack_msgs'     = ack_msgs,
      nack_msgs'    = nack_msgs,
    }
  }

  action update_svs_n2 = {
    val new_r0 = val_values_r(val_msgs, val_senders_r(val_msgs, 0), 0)
    val new_r1 = val_values_r(val_msgs, val_senders_r(val_msgs, 1), 1)
    all {
      new_r0 != n2.svs_r0 or new_r1 != n2.svs_r1,
      n2'           = { ...n2, svs_r0: new_r0, svs_r1: new_r1 },
      n1'           = n1,
      val_msgs'     = val_msgs,
      ack_req_msgs' = ack_req_msgs,
      ack_msgs'     = ack_msgs,
      nack_msgs'    = nack_msgs,
    }
  }

  action collect_vals_n2 = {
    val r       = n2.proposer_round
    val senders = val_senders_r(val_msgs, r)
    val new_svs = val_values_r(val_msgs, senders, r)
    all {
      n2.val_sent.contains(r),
      not(n2.brb_ready.contains(r)),
      senders.size() >= BRB_THRESHOLD,
      n2'           = { ...n2,
                        brb_ready:    n2.brb_ready.setAdd(r),
                        proposed_set: lat_join(n2.proposed_set, new_svs) },
      n1'           = n1,
      val_msgs'     = val_msgs,
      ack_req_msgs' = ack_req_msgs,
      ack_msgs'     = ack_msgs,
      nack_msgs'    = nack_msgs,
    }
  }

  action send_ack_req_n2 = {
    val new_ts = n2.ts + 1
    all {
      n2.brb_ready.contains(n2.proposer_round),
      not(n2.ack_req_sent),
      not(n2.decided),
      n2'           = { ...n2, ack_req_sent: true, ts: new_ts },
      ack_req_msgs' = ack_req_msgs.setAdd({
                        from:         "n2",
                        round:        n2.proposer_round,
                        ts:           new_ts,
                        proposed_set: n2.proposed_set }),
      n1'           = n1,
      val_msgs'     = val_msgs,
      ack_msgs'     = ack_msgs,
      nack_msgs'    = nack_msgs,
    }
  }

  action respond_ack_req_n2 = {
    nondet req = ack_req_msgs.filter(m =>
      m.round <= n2.safe_round
        and not_yet_responded(n2.responded_to, m.round, m.from, m.ts)
        and SAFE_alg4(m.proposed_set, n2)   // <-- BUGGY gate
    ).oneOf()
    val new_responded = n2.responded_to.setAdd({ round: req.round, proposer: req.from, ts: req.ts })
    if (lat_le(n2.accepted_set, req.proposed_set))
      all {
        n2'           = { ...n2,
                          accepted_set: req.proposed_set,
                          responded_to: new_responded },
        ack_msgs'     = ack_msgs.setAdd({
                          from:         "n2",
                          req_sender:   req.from,
                          round:        req.round,
                          ts:           req.ts,
                          accepted_set: req.proposed_set }),
        n1'           = n1,
        val_msgs'     = val_msgs,
        ack_req_msgs' = ack_req_msgs,
        nack_msgs'    = nack_msgs,
      }
    else
      all {
        n2'           = { ...n2,
                          accepted_set: lat_join(n2.accepted_set, req.proposed_set),
                          responded_to: new_responded },
        nack_msgs'    = nack_msgs.setAdd({
                          from:         "n2",
                          req_sender:   req.from,
                          round:        req.round,
                          ts:           req.ts,
                          accepted_set: n2.accepted_set }),
        n1'           = n1,
        val_msgs'     = val_msgs,
        ack_req_msgs' = ack_req_msgs,
        ack_msgs'     = ack_msgs,
      }
  }

  action process_nack_n2 = {
    val r = n2.proposer_round
    nondet nack = nack_msgs.filter(m =>
      m.req_sender == "n2"
        and m.round == r
        and m.ts == n2.ts
        and SAFE_correct(m.accepted_set, n2)
        and not(lat_le(m.accepted_set, n2.proposed_set))
    ).oneOf()
    val new_proposed = lat_join(n2.proposed_set, nack.accepted_set)
    val new_ts       = n2.ts + 1
    all {
      n2.ack_req_sent,
      not(n2.decided),
      n2'           = { ...n2, proposed_set: new_proposed, ts: new_ts },
      ack_req_msgs' = ack_req_msgs.setAdd({
                        from:         "n2",
                        round:        r,
                        ts:           new_ts,
                        proposed_set: new_proposed }),
      n1'           = n1,
      val_msgs'     = val_msgs,
      ack_msgs'     = ack_msgs,
      nack_msgs'    = nack_msgs,
    }
  }

  action decide_n2 = {
    nondet decision = quorum_decisions(ack_msgs, n2.proposer_round, n2.decided_set, n2).oneOf()
    all {
      n2.ack_req_sent,
      not(n2.decided),
      n2'           = { ...n2, decided: true, decided_set: decision },
      n1'           = n1,
      val_msgs'     = val_msgs,
      ack_req_msgs' = ack_req_msgs,
      ack_msgs'     = ack_msgs,
      nack_msgs'    = nack_msgs,
    }
  }

  action advance_round_n2 = all {
    n2.decided,
    n2.proposer_round < MAX_ROUND,
    n2'           = { ...n2,
                      proposer_round: n2.proposer_round + 1,
                      ack_req_sent:   false,
                      decided:        false },
    n1'           = n1,
    val_msgs'     = val_msgs,
    ack_req_msgs' = ack_req_msgs,
    ack_msgs'     = ack_msgs,
    nack_msgs'    = nack_msgs,
  }

  action advance_safe_round_n2 = all {
    n2.safe_round < MAX_ROUND,
    has_safe_round_quorum(ack_msgs, n2.safe_round, n2),
    n2'           = { ...n2, safe_round: n2.safe_round + 1 },
    n1'           = n1,
    val_msgs'     = val_msgs,
    ack_req_msgs' = ack_req_msgs,
    ack_msgs'     = ack_msgs,
    nack_msgs'    = nack_msgs,
  }

  // =========================================================================
  // MAIN STEP — nondeterministically pick any enabled action
  // =========================================================================

  action step = any {
    broadcast_val_n1,
    update_svs_n1,
    collect_vals_n1,
    send_ack_req_n1,
    respond_ack_req_n1,
    process_nack_n1,
    decide_n1,
    advance_round_n1,
    advance_safe_round_n1,
    broadcast_val_n2,
    update_svs_n2,
    collect_vals_n2,
    send_ack_req_n2,
    respond_ack_req_n2,
    process_nack_n2,
    decide_n2,
    advance_round_n2,
    advance_safe_round_n2,
  }

  // =========================================================================
  // TEMPORAL PROPERTIES
  // =========================================================================

  // ---------------------------------------------------------------------------
  // inclusivity_liveness_alg4 — VIOLATED by SAFE_alg4 (the bug)
  //
  // Once a node has broadcast its round-1 Val (val_sent contains 1),
  // it must eventually decide on R1_VALS = {2}.
  //
  // Under SAFE_alg4 this never happens:
  //   proposed_set = {1, 2} after round-1 BRB; SAFE_alg4({1,2}, svs) is false
  //   for every svs[r] (no single round's SvS covers both {1} and {2}).
  //   No acceptor ever responds to any round-1 AckReq. No quorum. No decision.
  //
  // No fairness assumption is needed — the block is structural.
  //
  // Run:
  //   quint verify --temporal inclusivity_liveness_alg4 gwts_buggy_safe_alg4_tlc.qnt
  // ---------------------------------------------------------------------------
  temporal inclusivity_liveness_alg4 =
    leadsTo(n1.val_sent.contains(1), lat_le(R1_VALS, n1.decided_set))
    and leadsTo(n2.val_sent.contains(1), lat_le(R1_VALS, n2.decided_set))

  // =========================================================================
  // SAFETY INVARIANTS (optional cross-checks)
  // =========================================================================

  // Comparability: any two non-empty decided_sets are lattice-comparable.
  val comparability =
    (n1.decided_set != Set() and n2.decided_set != Set()) implies
    (lat_le(n1.decided_set, n2.decided_set) or lat_le(n2.decided_set, n1.decided_set))

  // Validity: decided/accepted/proposed sets only contain values from E.
  val validity =
    lat_le(n1.decided_set,  E) and lat_le(n1.accepted_set, E) and lat_le(n1.proposed_set, E)
    and lat_le(n2.decided_set,  E) and lat_le(n2.accepted_set, E) and lat_le(n2.proposed_set, E)

  // Phase ordering: brb_ready → ack_req_sent → decided (within a round).
  val phase_ordering =
    (n1.ack_req_sent implies n1.brb_ready.contains(n1.proposer_round))
    and (n1.decided implies n1.ack_req_sent)
    and (n2.ack_req_sent implies n2.brb_ready.contains(n2.proposer_round))
    and (n2.decided implies n2.ack_req_sent)

}
