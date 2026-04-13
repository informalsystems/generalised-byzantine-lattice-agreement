// -*- mode: Bluespec; -*-
// Generalized Byzantine Lattice Agreement — GWTS Algorithm (Multi-Round)
//
// Based on: "Byzantine Generalized Lattice Agreement"
// Authors: G.A. Di Luna, E. Anceaume, L. Querzoni (2020), arXiv:1910.05768
//
// GWTS extends WTS (single-shot) to an infinite sequence of LA instances.
// Each round r runs the WTS two-phase protocol with these GWTS differences:
//
//   proposed_set accumulates: V_p (lattice values for process p) grows by
//     joining received values across rounds; it is never reset. ValMsg carries
//     only batch[r] (the new values for round r), not the full proposed_set.
//
//   accepted accumulates: a single Set[InputValue] that grows monotonically
//     across all rounds. Never reset.
//
//   ts (timestamp): a per-process counter incremented each time the proposer
//     (re-)broadcasts an AckReqMsg. Acceptors track the last ts responded to
//     per (round, proposer) and only respond to strictly newer ones (SAFE).
//
//   SAFE: acceptor responds only if every value in the proposal is covered by
//     some round's SvS — ∀v ∈ proposed. ∃r. v ∈ svs[r]. Different values may
//     come from different rounds' SvS. One function serves both AckReq eligibility
//     (previously called SAFEA) and nack filtering.
//
//   safe_round counter: each acceptor gates on r <= safe_round. Advances
//     when byz_quorum AckMsgs matching the same (Accepted_set, destination,
//     ts, r) are observed for r = safe_round.
//     destination may be ANY proposer — not necessarily this node. The
//     acceptor is detecting a legitimate end for some proposer's round r,
//     regardless of its own proposer role. Independent of the proposer's
//     decide transition, which advances proposer_round.
//     Both transitions may fire from the same quorum observation.
//
//   Broadcast Acks: AckMsg is broadcast to all, enabling legit-end detection.
//
// Safety properties for multi-round setting:
//   Comparability: any two decided_sets are lattice-comparable (one subsumes the other).
//   Local Stability: decided_set never shrinks across rounds (D_r ⊆ D_{r+1}).

module GWTSLatticeAgreement {
  import basicSpells.* from "choreo/spells/basicSpells"
  import choreo(processes = NODES) as choreo from "choreo/choreo"

  // =========================================================================
  // PROTOCOL-SPECIFIC TYPES
  // =========================================================================

  // Positive integers in [1, 2^31-1] are valid proposable values (correct nodes).
  // Byzantine nodes may inject values in (2^31-1, 2^32-1] to probe validity filters.
  type InputValue = int

  // =========================================================================
  // MANDATORY CHOREO TYPES
  // =========================================================================

  type Node = str

  // All messages carry a round number.
  // AckReqMsg/AckMsg/NackMsg also carry ts (AckReq sequence number).
  type Message =
    | ValMsg({ from: Node, round: int, values: Set[InputValue] })
      // Phase 1: simplified BRB (Byzantine Reliable Broadcast) per round; carries batch[r] (new values for that round only)
    | AckReqMsg({ from: Node, round: int, ts: int, proposed_set: Set[InputValue] })
      // Phase 2: proposer broadcasts AckReq for its current proposal; ts increments on retry
    | AckMsg({ from: Node, req_sender: Node, round: int, ts: int, accepted_set: Set[InputValue] })
      // Phase 2: acceptor acks — BROADCAST so all can observe legit ends
    | NackMsg({ from: Node, req_sender: Node, round: int, ts: int, accepted_set: Set[InputValue] })
      // Phase 2: acceptor nacks — sent to proposer only; carries updated accepted set

  // Per-process local state
  type StateFields = {
    // --- Proposer ---
    proposer_round: int,                  // current round this process is proposing in
    proposed_set:   Set[InputValue],      // V_p: accumulates across all rounds, never reset
    ts:             int,                  // AckReq timestamp; incremented on each retry
    ack_req_sent:   bool,                 // sent AckReq for current proposer_round
    decided:        bool,                 // decided in current proposer_round, reset on advance
    decided_set:    Set[InputValue],      // accumulates all decided values across rounds, never reset

    // --- Acceptor ---
    safe_round:     int,                  // process rounds 0..safe_round only (GWTS gating)
    accepted_set:   Set[InputValue],      // accumulates across all rounds, never reset
    responded_to:   Set[{ round: int, proposer: Node, ts: int }], // (round, proposer, ts) triples already responded to; enables SAFE condition

    // --- Phase 1 per round ---
    val_sent:       Set[int],               // rounds where ValMsg was broadcast
    svs:            int -> Set[InputValue], // SvS_r per round (built from BRB quorum)
    brb_ready:      Set[int],               // rounds where BRB phase completed
    pre_disclose_val_senders: int -> Set[Node], // Val senders already known when disclosing started per round
  }

  type ActionTaken =
    | Init
    | BroadcastVal     ({ node: Node })
    | UpdateSvs        ({ node: Node, round: int, new_svs: Set[InputValue] })
    | CollectVals      ({ node: Node })
    | SendAckReq       ({ node: Node })
    | RespondAckReq    ({ node: Node, round: int, proposer: Node, ts: int })
    | ProcessNack      ({ node: Node, received_set: Set[InputValue] })
    | Decide           ({ node: Node, decision: Set[InputValue] })
    | AdvanceRound     ({ node: Node })
    | AdvanceSafeRound ({ node: Node })
    | ByzDisclose      ({ node: Node, target: Node, round: int, values: Set[InputValue] })
    | ByzAckReq        ({ node: Node, round: int, ts: int, proposed_set: Set[InputValue] })
    | ByzNack          ({ node: Node, target: Node, round: int, ts: int, accepted_set: Set[InputValue] })
    | ByzAck           ({ node: Node, req_sender: Node, round: int, ts: int, accepted_set: Set[InputValue] })

  type CustomEffects = ActionTaken
  type Event        = ()
  type Extensions   = { actionTaken: ActionTaken }

  // =========================================================================
  // BOILERPLATE (do not modify)
  // =========================================================================

  type LocalState   = choreo::LocalState[Node, StateFields]
  type LocalContext = choreo::LocalContext[Node, StateFields, Message, Event, Extensions]
  type Transition   = choreo::Transition[Node, StateFields, Message, Event, CustomEffects]
  type GlobalContext = choreo::GlobalContext[Node, StateFields, Message, Event, Extensions]

  // =========================================================================
  // PROTOCOL CONFIGURATION
  // =========================================================================

  const N:            int
  const F:            int
  const NODES:        Set[Node]
  const BATCH_VALUES: Node -> (int -> Set[InputValue])    // new values per node per round (batch[r])
  const MAX_ROUND:    int    // upper bound on rounds for finite simulation
  const BYZ_NODES:   Set[Node]           // nodes that may take Byzantine actions
  const BYZ_VALUES:  Set[InputValue]     // fabricated values outside any batch (not in E)

  // Semantic range constants (informational — Quint uses arbitrary integers).
  // Correct nodes propose values in [1, INT32_MAX].
  // Byzantine nodes may inject values in (INT32_MAX, UINT32_MAX].
  pure val INT32_MAX:  int = 2147483647   // 2^31 - 1
  pure val UINT32_MAX: int = 4294967295   // 2^32 - 1

  // Byzantine quorum: ⌊(N+F)/2⌋ + 1. For N=4, F=1: 3
  pure val byz_quorum: int = (N + F) / 2 + 1

  // BRB delivery threshold. For N=4, F=1: 3
  pure val brb_threshold: int = N - F

  // Upper bound on ts values a Byzantine node may inject to influence correct
  // nodes. A correct proposer's ts starts at 1 and grows by 1 per AckReq/Nack
  // cycle, with at most (MAX_ROUND + 1) rounds. N * (MAX_ROUND + 1) is a safe
  // overapproximation covering all reachable ts values any correct node may use.
  pure val byz_ts_bound: int = N * (MAX_ROUND + 1)

  // =========================================================================
  // LATTICE OPERATIONS
  // =========================================================================

  pure def lat_join(v1: Set[InputValue], v2: Set[InputValue]): Set[InputValue] =
    v1.union(v2)

  pure def lat_le(v1: Set[InputValue], v2: Set[InputValue]): bool =
    v1.forall(x => v2.contains(x))

  pure def join_all(sets: Set[Set[InputValue]]): Set[InputValue] =
    sets.fold(Set(), (acc, vs) => acc.union(vs))

  // =========================================================================
  // HELPER FUNCTIONS
  // =========================================================================

  // SAFE condition: every value in `proposed` is covered by some round's SvS.
  // Formally: ∀v ∈ proposed. ∃r ∈ [0, MAX_ROUND]. v ∈ svs[r].
  // Different values may come from different rounds — only per-element coverage
  // is required, not containment in a single round's SvS.
  //
  // This single predicate is used in two roles:
  //   • AckReq eligibility (acceptor gate, formerly "SAFEA"): ensures every
  //     value in the proposer's set was properly disclosed before accepting.
  //   • Nack filtering (proposer side): ensures nacked accepted_sets only carry
  //     values from legitimate disclosures, blocking Byzantine fabrications.
  // max_round is the round of the message being evaluated — only svs[0..max_round]
  // counts as legitimately reached at that point in the protocol. Checking future
  // rounds (up to MAX_ROUND) would allow Byzantine-seeded svs entries for rounds
  // not yet completed to satisfy the check prematurely.
  pure def SAFE(proposed: Set[InputValue], svs: int -> Set[InputValue], max_round: int): bool =
    proposed.forall(v => 0.to(max_round).exists(r => svs.get(r).contains(v)))

  // not_yet_responded: this exact (round, proposer, ts) triple has not been
  // responded to before. Faithfully models the original algorithm's removal of
  // processed messages from waiting_msgs: each (round, proposer, ts) is handled
  // at most once, but there is no ts-ordering constraint — an acceptor may
  // respond to ts=1 after ts=2 for the same (round, proposer), matching the
  // algorithm's behaviour when both ack_reqs are buffered simultaneously.
  pure def not_yet_responded(
    responded_to: Set[{ round: int, proposer: Node, ts: int }],
    round:        int,
    proposer:     Node,
    ts:           int
  ): bool =
    not(responded_to.contains({ round: round, proposer: proposer, ts: ts }))

  // =========================================================================
  // MESSAGE HELPERS
  // =========================================================================

  // ValMsg senders for a specific round whose entire value_set belongs to E
  // Filters out invalid/Byzantine disclosures at the source so that svs and
  // proposed_set are never polluted with fabricated values.
  pure def get_val_senders_r(messages: Set[Message], round: int): Set[Node] =
    messages.filterMap(m => match m {
      | ValMsg(v) =>
        if (v.round == round and lat_le(v.values, all_batch_values)) Some(v.from) else None
      | _ => None
    })

  // Union of value sets in ValMsgs for a round, from given senders.
  // E-validity is re-checked per message: a Byzantine node may pass the sender
  // filter (because one of its ValMsgs is valid) yet also send a second ValMsg
  // with fabricated values. Filtering per message prevents those from leaking
  // into svs or proposed_set.
  pure def get_val_values_r(messages: Set[Message], senders: Set[Node], round: int): Set[InputValue] =
    join_all(messages.filterMap(m => match m {
      | ValMsg(v) =>
        if (v.round == round and senders.contains(v.from) and lat_le(v.values, all_batch_values))
          Some(v.values)
        else None
      | _ => None
    }))

  // Eligible AckReqMsgs to respond to: not_yet_responded + SAFE + safe_round gate.
  // not_yet_responded: ts strictly greater than last responded ts.
  // SAFE: every value in proposed is covered by some round's SvS (see SAFE def above).
  // Gate: round <= safe_round.
  pure def get_eligible_ack_reqs(
    messages:     Set[Message],
    responded_to: Set[{ round: int, proposer: Node, ts: int }],
    safe_round:   int,
    svs:          int -> Set[InputValue]
  ): Set[{ round: int, proposer: Node, ts: int, proposed_set: Set[InputValue] }] =
    messages.filterMap(m => match m {
      | AckReqMsg(r) =>
        if (r.round <= safe_round
          and not_yet_responded(responded_to, r.round, r.from, r.ts)
          and SAFE(r.proposed_set, svs, r.round))
          Some({ round: r.round, proposer: r.from, ts: r.ts, proposed_set: r.proposed_set })
        else None
      | _ => None
    })

  // All accepted_sets for a given round that have a byz_quorum of distinct
  // ack senders AND cover prev_decision.
  // Per the paper, any correct proposer can decide on any accepted_set that
  // has been correctly accepted in round r — destination need not be self.
  // Groups by (accepted_set, req_sender, ts, round): destination and ts are
  // named fields in the pseudocode (not wildcards), so they are fixed within
  // the quorum. Only the ack sender varies (the * wildcard).
  // SAFE check: apply SAFE before adding an ack to ack_history; only acks
  // in ack_history contribute to decisions. Acks with fabricated accepted_set
  // values (outside E) fail SAFE and are excluded.
  // Local Stability is enforced by lat_le(prev_decision, accepted_set).
  pure def get_quorum_decisions(
    messages:      Set[Message],
    round:         int,
    prev_decision: Set[InputValue],
    svs:           int -> Set[InputValue]
  ): Set[Set[InputValue]] =
    val acks = messages.filterMap(m => match m {
      | AckMsg(a) => if (a.round == round and SAFE(a.accepted_set, svs, round)) Some(a) else None
      | _ => None
    })
    acks.filterMap(a =>
      val quorum_senders =
        acks.filter(a2 =>
          a2.accepted_set == a.accepted_set
            and a2.req_sender == a.req_sender
            and a2.ts == a.ts
        ).map(a2 => a2.from)
      if (quorum_senders.size() >= byz_quorum
        and lat_le(prev_decision, a.accepted_set))
        Some(a.accepted_set)
      else None
    )

  // NackMsgs addressed to me for my current (round, ts).
  // SAFE check: applied to the lattice element carried in the nack, which is 
  // accepted_set (Rcvd_set in the paper). A Byzantine acceptor that sends a nack 
  // with fabricated values outside E will have those values absent from every 
  // svs[r], so SAFE fails and the nack is ignored.
  pure def get_nacks_for_me(
    messages: Set[Message],
    self:     Node,
    round:    int,
    ts:       int,
    svs:      int -> Set[InputValue]
  ): Set[Set[InputValue]] =
    messages.filterMap(m => match m {
      | NackMsg(n) =>
        if (n.req_sender == self and n.round == round and n.ts == ts
          and SAFE(n.accepted_set, svs, round))
          Some(n.accepted_set)
        else None
      | _ => None
    })

  // Detect a legitimate-end quorum for a given round: byz_quorum acks 
  // matching the same (accepted_set, req_sender, ts) for that round. 
  // req_sender (= destination in the paper) can be ANY proposer.
  // SAFE check: apply SAFE_A before adding an ack to ack_history;
  // safe_r advancement only looks at ack_history.
  pure def get_safe_round_quorums(
    messages: Set[Message],
    round:    int,
    svs:      int -> Set[InputValue]
  ): Set[{ accepted_set: Set[InputValue], destination: Node, ts: int }] =
    val acks = messages.filterMap(m => match m {
      | AckMsg(a) => if (a.round == round and SAFE(a.accepted_set, svs, round)) Some(a) else None
      | _ => None
    })
    acks.filterMap(a =>
      val quorum_senders =
        acks.filter(a2 =>
          a2.accepted_set == a.accepted_set
            and a2.req_sender == a.req_sender
            and a2.ts == a.ts
        ).map(a2 => a2.from)
      if (quorum_senders.size() >= byz_quorum)
        Some({ accepted_set: a.accepted_set, destination: a.req_sender, ts: a.ts })
      else None
    )

  // =========================================================================
  // PHASE 1 TRANSITIONS (per round)
  // =========================================================================

  // T1: Broadcast ValMsg for current proposer_round.
  // On entering a new round, union batch[round] into proposed_set, then
  // broadcast batch[round] (not the full accumulated set).
  // Guard: not yet sent ValMsg for this round, within MAX_ROUND.
  pure def listen_broadcast_val(ctx: LocalContext): Set[()] =
    val s = ctx.state
    val r = s.proposer_round
    if (not(s.val_sent.contains(r))
      and s.proposer_round <= MAX_ROUND)
      Set(())
    else Set()

  pure def handle_broadcast_val(ctx: LocalContext, _u: ()): Transition = {
    val s     = ctx.state
    val r     = s.proposer_round
    val batch = BATCH_VALUES.get(s.process_id).get(r)   // new values for this round
    val new_proposed = lat_join(s.proposed_set, batch)
    // Snapshot Val senders already known before disclosing: their values arrived
    // before our disclosing state and must not be added to proposed_set.
    val pre_disclose_senders = get_val_senders_r(ctx.messages, r)
    {
      effects: Set(
        choreo::Broadcast(
          ValMsg({ from: s.process_id, round: r, values: batch })  // broadcast batch[r]
        ),
        choreo::CustomEffect(BroadcastVal({ node: s.process_id }))
      ),
      post_state: {
        ...s,
        proposed_set: new_proposed,
        val_sent:     s.val_sent.setAdd(r),
        pre_disclose_val_senders: s.pre_disclose_val_senders.set(r, pre_disclose_senders),
      }
    }
  }

  // T_svs: Continuously update svs[r] as new ValMsgs arrive
  // "svs[r] = svs[r] UNION value_set — always, regardless of own round/state".
  // A node may receive ValMsgs for any round (nodes advance at different speeds),
  // so we check all rounds and emit an update for each one that has grown.
  pure def listen_update_svs(ctx: LocalContext): Set[{ round: int, new_svs: Set[InputValue] }] =
    val s = ctx.state
    0.to(MAX_ROUND).fold(Set(), (acc, r) =>
      val new_svs = get_val_values_r(ctx.messages, get_val_senders_r(ctx.messages, r), r)
      if (new_svs != s.svs.get(r))
        acc.union(Set({ round: r, new_svs: new_svs }))
      else acc
    )

  pure def handle_update_svs(ctx: LocalContext, params: { round: int, new_svs: Set[InputValue] }): Transition = {
    val s = ctx.state
    {
      effects: Set(choreo::CustomEffect(UpdateSvs({ node: s.process_id, round: params.round, new_svs: params.new_svs }))),
      post_state: { ...s, svs: s.svs.set(params.round, params.new_svs) }
    }
  }

  // T2: Collect enough ValMsgs to build SvS for current round.
  // not(brb_ready) implies not(ack_req_sent) by phase_ordering, so it serves as
  // both the "state == disclosing" check and a guard against re-firing.
  pure def listen_collect_vals(ctx: LocalContext): Set[()] =
    val s = ctx.state
    val r = s.proposer_round
    val senders = get_val_senders_r(ctx.messages, r)
    if (s.val_sent.contains(r)
      and not(s.brb_ready.contains(r))
      and senders.size() >= brb_threshold)
      Set(())
    else Set()

  pure def handle_collect_vals(ctx: LocalContext, _u: ()): Transition = {
    val s       = ctx.state
    val r       = s.proposer_round
    val senders = get_val_senders_r(ctx.messages, r)
    // Only include ValMsgs from senders who were NOT already known when disclosing
    // started (proposed_set only accumulates from ValMsgs received while in disclosing 
    // state, not before).
    val post_disclose_senders = senders.filter(n => not(s.pre_disclose_val_senders.get(r).contains(n)))
    val new_svs      = get_val_values_r(ctx.messages, post_disclose_senders, r)
    val new_proposed = lat_join(s.proposed_set, new_svs)
    {
      effects: Set(choreo::CustomEffect(CollectVals({ node: s.process_id }))),
      post_state: {
        ...s,
        brb_ready:    s.brb_ready.setAdd(r),
        proposed_set: new_proposed,
      }
    }
  }

  // =========================================================================
  // PHASE 2 TRANSITIONS (per round)
  // =========================================================================

  // T3: Broadcast initial AckReqMsg for current proposer_round.
  // Guard: BRB done, AckReq not yet sent, not decided this round.
  pure def listen_send_ack_req(ctx: LocalContext): Set[()] =
    val s = ctx.state
    if (s.brb_ready.contains(s.proposer_round)
      and not(s.ack_req_sent)
      and not(s.decided))
      Set(())
    else Set()

  pure def handle_send_ack_req(ctx: LocalContext, _u: ()): Transition = {
    val s      = ctx.state
    val new_ts = s.ts + 1
    {
      effects: Set(
        choreo::Broadcast(
          AckReqMsg({ from: s.process_id, round: s.proposer_round, ts: new_ts, proposed_set: s.proposed_set })
        ),
        choreo::CustomEffect(SendAckReq({ node: s.process_id }))
      ),
      post_state: { ...s, ack_req_sent: true, ts: new_ts }
    }
  }

  // T4: Respond to an eligible AckReqMsg (acceptor role).
  // SAFE: every value in proposed_set covered by some round's SvS (∀v. ∃r. v ∈ svs[r]).
  // Gate:  round <= safe_round.
  // ACK branch:  accepted_set ⊆ proposed_set — safe to raise accepted to proposed.
  // NACK branch: accepted_set ⊄ proposed_set — union and send back; proposer must raise proposal.
  pure def listen_respond_ack_req(
    ctx: LocalContext
  ): Set[{ round: int, proposer: Node, ts: int, proposed_set: Set[InputValue] }] =
    val s = ctx.state
    get_eligible_ack_reqs(ctx.messages, s.responded_to, s.safe_round, s.svs)

  pure def handle_respond_ack_req(
    ctx:    LocalContext,
    params: { round: int, proposer: Node, ts: int, proposed_set: Set[InputValue] }
  ): Transition = {
    val s             = ctx.state
    val r             = params.round
    val p             = params.proposer
    val t             = params.ts
    val received_set  = params.proposed_set
    val new_responded = s.responded_to.setAdd({ round: r, proposer: p, ts: t })
    if (lat_le(s.accepted_set, received_set)) {
      // ACK: accepted_set ⊆ V — raise accepted_set to V and broadcast Ack
      {
        effects: Set(
          choreo::Broadcast(
            AckMsg({ from: s.process_id, req_sender: p, round: r, ts: t, accepted_set: received_set })
          ),
          choreo::CustomEffect(RespondAckReq({ node: s.process_id, round: r, proposer: p, ts: t }))
        ),
        post_state: {
          ...s,
          accepted_set: received_set,
          responded_to: new_responded,
        }
      }
    } else {
      // NACK: accepted_set ⊄ V — send old accepted_set back to proposer, then union locally.
      val new_accepted = lat_join(s.accepted_set, received_set)
      {
        effects: Set(
          choreo::Send({
            to: p,
            message: NackMsg({
              from:         s.process_id,
              req_sender:   p,
              round:        r,
              ts:           t,
              accepted_set: s.accepted_set  // old value, before union
            })
          }),
          choreo::CustomEffect(RespondAckReq({ node: s.process_id, round: r, proposer: p, ts: t }))
        ),
        post_state: {
          ...s,
          accepted_set: new_accepted,       // updated to union after sending
          responded_to: new_responded,
        }
      }
    }
  }

  // T5: Process a Nack - join proposed_set with nacked value, increment ts,
  // and immediately re-broadcast AckReq.
  // Stale nacks (whose accepted_set ⊆ proposed_set) are filtered out to avoid stutter steps.
  // Guard: ack_req sent for current round and ts, not yet decided.
  pure def listen_process_nack(ctx: LocalContext): Set[Set[InputValue]] =
    val s = ctx.state
    val r = s.proposer_round
    if (s.ack_req_sent and not(s.decided))
      get_nacks_for_me(ctx.messages, s.process_id, r, s.ts, s.svs)
        .filter(received_set => not(lat_le(received_set, s.proposed_set)))
    else Set()

  pure def handle_process_nack(ctx: LocalContext, received_set: Set[InputValue]): Transition = {
    val s           = ctx.state
    val new_proposed = lat_join(s.proposed_set, received_set)
    val new_ts       = s.ts + 1
    {
      // Immediately re-broadcast AckReq with updated proposal and new ts (line 35)
      effects: Set(
        choreo::Broadcast(
          AckReqMsg({
            from:         s.process_id,
            round:        s.proposer_round,
            ts:           new_ts,
            proposed_set: new_proposed
          })
        ),
        choreo::CustomEffect(ProcessNack({ node: s.process_id, received_set: received_set }))
      ),
      post_state: {
        ...s,
        proposed_set: new_proposed,
        ts:           new_ts,
      }
    }
  }

  // T6: Decide — any accepted_set for the current round with a byz_quorum 
  // of acks and covering decided_set (decided_set ⊆ accepted_set).
  // Acks are reliably broadcast, so a proposer can decide on any proposer's accepted_set.
  // Guard: ack_req sent (in Phase 2), not yet decided this round.
  pure def listen_decide(ctx: LocalContext): Set[Set[InputValue]] =
    val s = ctx.state
    val r = s.proposer_round
    if (s.ack_req_sent and not(s.decided))
      get_quorum_decisions(ctx.messages, r, s.decided_set, s.svs)
    else Set()

  pure def handle_decide(ctx: LocalContext, decision: Set[InputValue]): Transition = {
    val s = ctx.state
    {
      effects: Set(choreo::CustomEffect(Decide({ node: s.process_id, decision: decision }))),
      post_state: {
        ...s,
        decided:     true,
        decided_set: decision,  // listen_decide guards lat_le(s.decided_set, decision), so direct assignment is safe
      }
    }
  }

  // T7: Advance proposer_round after deciding.
  // safe_round is managed independently by handle_advance_safe_round
  // and may advance before or after proposer_round.
  pure def listen_advance_round(ctx: LocalContext): Set[()] =
    val s = ctx.state
    if (s.decided and s.proposer_round < MAX_ROUND)
      Set(())
    else Set()

  pure def handle_advance_round(ctx: LocalContext, _u: ()): Transition = {
    val s = ctx.state
    {
      effects: Set(choreo::CustomEffect(AdvanceRound({ node: s.process_id }))),
      post_state: {
        ...s,
        proposer_round: s.proposer_round + 1,
        ack_req_sent:   false,    // must re-send AckReq in new round
        decided:        false,    // reset for new round
        // proposed_set accumulates — not reset
        // decided_set accumulates — not reset
        // ts continues from previous round — timestamp is never resetted
        // safe_round is managed independently by handle_advance_safe_round
      }
    }
  }

  // T_safe_round: Advance safe_round upon observing a legitimate-end quorum
  // for the current safe_round. Any proposer's quorum suffices — destination 
  // need not be this node. Independent of deciding.
  pure def listen_advance_safe_round(
    ctx: LocalContext
  ): Set[{ accepted_set: Set[InputValue], destination: Node, ts: int }] =
    val s = ctx.state
    if (s.safe_round < MAX_ROUND)
      get_safe_round_quorums(ctx.messages, s.safe_round, s.svs)
    else Set()

  pure def handle_advance_safe_round(
    ctx:    LocalContext,
    _params: { accepted_set: Set[InputValue], destination: Node, ts: int }
  ): Transition = {
    val s = ctx.state
    {
      effects: Set(choreo::CustomEffect(AdvanceSafeRound({ node: s.process_id }))),
      post_state: { ...s, safe_round: s.safe_round + 1 }
    }
  }

  // =========================================================================
  // MAIN LISTENER
  // =========================================================================

  pure def main_listener(ctx: LocalContext): Set[Transition] =
    Set(
      // Correct-node transitions
      choreo::cue(ctx, listen_update_svs,              handle_update_svs),
      choreo::cue(ctx, listen_broadcast_val,           handle_broadcast_val),
      choreo::cue(ctx, listen_collect_vals,            handle_collect_vals),
      choreo::cue(ctx, listen_send_ack_req,            handle_send_ack_req),
      choreo::cue(ctx, listen_respond_ack_req,         handle_respond_ack_req),
      choreo::cue(ctx, listen_process_nack,            handle_process_nack),
      choreo::cue(ctx, listen_decide,                  handle_decide),
      choreo::cue(ctx, listen_advance_round,           handle_advance_round),
      choreo::cue(ctx, listen_advance_safe_round,      handle_advance_safe_round),
      // Byzantine transitions (enabled only for nodes in BYZ_NODES)
      choreo::cue(ctx, listen_byz_disclose,            handle_byz_disclose),
      choreo::cue(ctx, listen_byz_ack_req,             handle_byz_ack_req),
      choreo::cue(ctx, listen_byz_nack,                handle_byz_nack),
      choreo::cue(ctx, listen_byz_ack,                 handle_byz_ack),
    ).flatten()

  // =========================================================================
  // CUSTOM EFFECT PROCESSOR
  // =========================================================================

  pure def apply_custom_effect(ctx: GlobalContext, effect: CustomEffects): GlobalContext =
    { ...ctx, extensions: { actionTaken: effect } }

  // =========================================================================
  // INITIALIZATION
  // =========================================================================

  pure def initialize(n: Node): LocalState = {
    {
      process_id:     n,
      proposer_round: 0,
      proposed_set:   Set(),                  // starts empty; batch[r] merged in at each round's T1
      ts:             0,
      ack_req_sent:   false,
      decided:        false,
      decided_set:    Set(),
      safe_round:     0,
      accepted_set:   Set(),                  // starts empty; accumulates
      responded_to:   Set(),
      val_sent:       Set(),
      svs:            0.to(MAX_ROUND).mapBy(_ => Set()),
      brb_ready:      Set(),
      pre_disclose_val_senders: 0.to(MAX_ROUND).mapBy(_ => Set()),
    }
  }

  action init = choreo::init({
    system:     NODES.mapBy(n => initialize(n)),
    messages:   NODES.mapBy(_ => Set()),
    events:     NODES.mapBy(_ => Set()),
    extensions: { actionTaken: Init }
  })

  // =========================================================================
  // STEP
  // =========================================================================

  action step = choreo::step(main_listener, apply_custom_effect)

  // =========================================================================
  // WIRING
  // =========================================================================

  val s = choreo::s

  action step_with(v: Node, listener: LocalContext => Set[Transition]): bool =
    choreo::step_with(v, listener, apply_custom_effect)

  action step_deterministic(v: Node, listener: LocalContext => Transition): bool =
    choreo::step_deterministic(v, listener, apply_custom_effect)

  def with_cue(process, listen_fn, params) =
    choreo::with_cue(process, listen_fn, params)

  action perform(cue_ctx, upon_fn) =
    choreo::perform(cue_ctx, upon_fn, apply_custom_effect)

  // =========================================================================
  // BYZANTINE TRANSITIONS
  // =========================================================================
  //
  // listen functions return Set() for non-Byzantine nodes (guarded by BYZ_NODES),
  // so these transitions are invisible in the main_listener for correct nodes.
  // They do not modify local state — Byzantine nodes only inject messages.
  //
  // In test runs a specific Byzantine action can be forced via:
  //   .then(step_with("n4", ctx =>
  //       choreo::cue(ctx, _ => Set(<params>), handle_byz_xxx)))

  // B1: Equivocation — send different ValMsgs to different targets.
  // One option per (target, round, value) where value ranges over byz_value_pool.
  // Values from all_batch_values are legitimate; values from BYZ_VALUES are
  // fabricated and will be filtered by the E-validity check in get_val_senders_r.
  // Consecutive steps to different targets with different values model split-brain.
  pure def listen_byz_disclose(ctx: LocalContext): Set[{ target: Node, round: int, values: Set[InputValue] }] =
    val s = ctx.state
    if (BYZ_NODES.contains(s.process_id))
      NODES.fold(Set(), (acc, target) =>
        0.to(MAX_ROUND).fold(acc, (acc2, round) =>
          // Pool is per-round: only the Byzantine node's own preassigned batch
          // values for that round plus fabricated BYZ_VALUES. This prevents
          // a Byzantine node from disclosing other correct nodes' values.
          val pool = BATCH_VALUES.get(s.process_id).get(round).union(BYZ_VALUES)
          pool.fold(acc2,
            (acc3, v) => acc3.union(Set({ target: target, round: round, values: Set(v) }))
          )
        )
      )
    else Set()

  pure def handle_byz_disclose(
    ctx:    LocalContext,
    params: { target: Node, round: int, values: Set[InputValue] }
  ): Transition = {
    val s = ctx.state
    {
      effects: Set(
        choreo::Send({
          to:      params.target,
          message: ValMsg({ from: s.process_id, round: params.round, values: params.values })
        }),
        choreo::CustomEffect(ByzDisclose({ node: s.process_id, target: params.target, round: params.round, values: params.values }))
      ),
      post_state: s
    }
  }

  // B2: Broadcast AckReqMsg for any round with any proposed_set.
  // ts = s.ts + 1: the Byzantine node uses its own local ts counter, which grows
  // via repeated B2 steps, so it can eventually outbid any acceptor's responded_to
  // entry. One option per (round, value); manageable state space.
  pure def listen_byz_ack_req(ctx: LocalContext): Set[{ round: int, ts: int, proposed_set: Set[InputValue] }] =
    val s = ctx.state
    if (BYZ_NODES.contains(s.process_id))
      0.to(MAX_ROUND).fold(Set(), (acc, round) =>
        byz_value_pool.fold(acc,
          (acc2, v) => acc2.union(Set({ round: round, ts: s.ts + 1, proposed_set: Set(v) }))
        )
      )
    else Set()

  pure def handle_byz_ack_req(
    ctx:    LocalContext,
    params: { round: int, ts: int, proposed_set: Set[InputValue] }
  ): Transition = {
    val s = ctx.state
    {
      effects: Set(
        choreo::Broadcast(
          AckReqMsg({ from: s.process_id, round: params.round, ts: params.ts, proposed_set: params.proposed_set })
        ),
        choreo::CustomEffect(ByzAckReq({ node: s.process_id, round: params.round, ts: params.ts, proposed_set: params.proposed_set }))
      ),
      post_state: s
    }
  }

  // B3: Send NackMsg in response to an observed AckReqMsg with an arbitrary accepted_set.
  // ts is taken from a real observed AckReqMsg — proposers only process nacks where
  // n.ts == their current ts, so matching a live AckReq ts is both necessary and
  // sufficient. One option per (AckReq, value); manageable state space.
  // Values from BYZ_VALUES fail the SAFE check in get_nacks_for_me and are dropped
  // by the proposer; values from all_batch_values pass (once disclosed).
  pure def listen_byz_nack(ctx: LocalContext): Set[{ target: Node, round: int, ts: int, accepted_set: Set[InputValue] }] =
    val s = ctx.state
    if (BYZ_NODES.contains(s.process_id))
      val ack_reqs = ctx.messages.filterMap(m => match m {
        | AckReqMsg(a) => Some({ target: a.from, round: a.round, ts: a.ts })
        | _ => None
      })
      ack_reqs.fold(Set(), (acc, req) =>
        byz_value_pool.fold(acc,
          (acc2, v) => acc2.union(Set({ target: req.target, round: req.round, ts: req.ts, accepted_set: Set(v) }))
        )
      )
    else Set()

  pure def handle_byz_nack(
    ctx:    LocalContext,
    params: { target: Node, round: int, ts: int, accepted_set: Set[InputValue] }
  ): Transition = {
    val s = ctx.state
    {
      effects: Set(
        choreo::Send({
          to:      params.target,
          message: NackMsg({
            from:        s.process_id,
            req_sender:  params.target,
            round:       params.round,
            ts:          params.ts,
            accepted_set: params.accepted_set
          })
        }),
        choreo::CustomEffect(ByzNack({ node: s.process_id, target: params.target, round: params.round, ts: params.ts, accepted_set: params.accepted_set }))
      ),
      post_state: s
    }
  }

  // B4: Broadcast AckMsg for any req_sender, using (round, ts) from an observed AckReqMsg.
  // ts is taken from a live AckReqMsg to match quorum grouping in get_quorum_decisions
  // (grouped by accepted_set, req_sender, ts). req_sender ranges over ALL nodes —
  // more powerful than the original (which fixed req_sender to the AckReq's from),
  // letting Byzantine nodes fabricate acks "on behalf of" any proposer. One option
  // per (AckReq, req_sender, value); ts dimension stays bounded by observed AckReqs.
  pure def listen_byz_ack(ctx: LocalContext): Set[{ req_sender: Node, round: int, ts: int, accepted_set: Set[InputValue] }] =
    val s = ctx.state
    if (BYZ_NODES.contains(s.process_id))
      val ack_reqs = ctx.messages.filterMap(m => match m {
        | AckReqMsg(a) => Some({ round: a.round, ts: a.ts })
        | _ => None
      })
      ack_reqs.fold(Set(), (acc, req) =>
        NODES.fold(acc, (acc2, req_sender) =>
          byz_value_pool.fold(acc2,
            (acc3, v) => acc3.union(Set({ req_sender: req_sender, round: req.round, ts: req.ts, accepted_set: Set(v) }))
          )
        )
      )
    else Set()

  pure def handle_byz_ack(
    ctx:    LocalContext,
    params: { req_sender: Node, round: int, ts: int, accepted_set: Set[InputValue] }
  ): Transition = {
    val s = ctx.state
    {
      effects: Set(
        choreo::Broadcast(
          AckMsg({ from: s.process_id, req_sender: params.req_sender, round: params.round, ts: params.ts, accepted_set: params.accepted_set })
        ),
        choreo::CustomEffect(ByzAck({ node: s.process_id, req_sender: params.req_sender, round: params.round, ts: params.ts, accepted_set: params.accepted_set }))
      ),
      post_state: s
    }
  }

  // Named listeners for step_with in tests
  pure def do_broadcast_val(ctx: LocalContext): Set[Transition] =
    choreo::cue(ctx, listen_broadcast_val, handle_broadcast_val)

  pure def do_collect_vals(ctx: LocalContext): Set[Transition] =
    choreo::cue(ctx, listen_collect_vals, handle_collect_vals)

  pure def do_send_ack_req(ctx: LocalContext): Set[Transition] =
    choreo::cue(ctx, listen_send_ack_req, handle_send_ack_req)

  pure def do_decide(ctx: LocalContext): Set[Transition] =
    choreo::cue(ctx, listen_decide, handle_decide)

  pure def do_update_svs(ctx: LocalContext): Set[Transition] =
    choreo::cue(ctx, listen_update_svs, handle_update_svs)

  pure def do_respond_ack_req(ctx: LocalContext): Set[Transition] =
    choreo::cue(ctx, listen_respond_ack_req, handle_respond_ack_req)

  pure def do_process_nack(ctx: LocalContext): Set[Transition] =
    choreo::cue(ctx, listen_process_nack, handle_process_nack)

  pure def do_advance_round(ctx: LocalContext): Set[Transition] =
    choreo::cue(ctx, listen_advance_round, handle_advance_round)

  pure def do_advance_safe_round(ctx: LocalContext): Set[Transition] =
    choreo::cue(ctx, listen_advance_safe_round, handle_advance_safe_round)

  // =========================================================================
  // SAFETY INVARIANTS
  // =========================================================================

  // Comparability: any two processes that have decided have comparable decided sets.
  // Since decided_set accumulates monotonically, this holds across all rounds.
  val comparability =
    NODES.forall(p => NODES.forall(q => {
      val sp = s.system.get(p)
      val sq = s.system.get(q)
      if (sp.decided_set != Set() and sq.decided_set != Set())
        lat_le(sp.decided_set, sq.decided_set)
          or lat_le(sq.decided_set, sp.decided_set)
      else true
    }))

  // Validity: every value in decided_set was proposed by some node in some round.
  pure val all_batch_values: Set[InputValue] =
    NODES.fold(Set(), (acc, n) =>
      0.to(MAX_ROUND).fold(acc, (acc2, r) => acc2.union(BATCH_VALUES.get(n).get(r))))

  // All values a Byzantine node may inject: legitimate values (for equivocation)
  // plus fabricated values outside E (for validity attacks).
  pure val byz_value_pool: Set[InputValue] = all_batch_values.union(BYZ_VALUES)

  // Lemma: No fabrication at any stage.
  // decided_set, accepted_set, and proposed_set must only contain values from
  // legitimate disclosures. Together these cover the full pipeline:
  //   BATCH_VALUES → proposed_set → accepted_set → decided_set
  val validity =
    NODES.forall(p => {
      val sp = s.system.get(p)
      lat_le(sp.decided_set, all_batch_values)
        and lat_le(sp.accepted_set, all_batch_values)
        and lat_le(sp.proposed_set, all_batch_values)
    })

  // Lemma: SVS E-validity.
  // svs[r] can only contain values from E (all_batch_values). This is guaranteed
  // by the E-validity filter in get_val_senders_r, even with Byzantine nodes.
  // Note: per-round tightness (svs[r] ⊆ round_batch_values(r)) holds only for
  // correct executions — a Byzantine node may disclose round-k values in a
  // round-r ValMsg and all correct nodes will accept them into svs[r] since the
  // algorithm's E check is not round-specific.
  pure def round_batch_values(r: int): Set[InputValue] =
    NODES.fold(Set(), (acc, n) => acc.union(BATCH_VALUES.get(n).get(r)))

  val svs_validity =
    NODES.forall(p => {
      val sp = s.system.get(p)
      0.to(MAX_ROUND).forall(r => lat_le(sp.svs.get(r), all_batch_values))
    })

  // Phase ordering: the protocol phases occur in order within each round.
  //   val_sent → brb_ready → ack_req_sent → decided
  val phase_ordering =
    NODES.forall(p => {
      val sp = s.system.get(p)
      val r  = sp.proposer_round
      // BRB cannot complete without having first sent a ValMsg
      sp.brb_ready.forall(r2 => sp.val_sent.contains(r2))
        // AckReq cannot be sent without BRB completing first
        and (sp.ack_req_sent implies sp.brb_ready.contains(r))
        // Cannot decide without having sent an AckReq
        and (sp.decided implies sp.ack_req_sent)
    })

  // Combined safety invariant
  val safety = comparability
    and validity
    and svs_validity
    and phase_ordering


  // =========================================================================
  // WITNESSES
  // =========================================================================

  // Witness: a decision is reachable.
  // Holds until some node decides; Quint reports the violating trace as the
  // example execution showing a decision.
  // Run with: quint run --invariant never_decided gwts_lattice_agreement.qnt --main gwts_standard
  val never_decided =
    NODES.forall(p => not(s.system.get(p).decided))

  // Witness: round 1 is reachable.
  // Holds until some node advances to proposer_round=1.
  // Run with: quint run --invariant never_round1 gwts_lattice_agreement.qnt --main gwts_standard
  val never_round1 =
    NODES.forall(p => s.system.get(p).proposer_round < 1)

  // Witness: safe_round advancement is reachable.
  // Holds until some acceptor's safe_round increments beyond 0.
  // Run with: quint run --invariant never_safe_advance gwts_lattice_agreement.qnt --main gwts_standard
  val never_safe_advance =
    NODES.forall(p => s.system.get(p).safe_round == 0)

  // Witness: both ACK and NACK acceptor code paths are reachable.
  //
  // ACK path signature: some acceptor's accepted_set is non-empty — it was
  //   raised to match a proposer's proposed_set via the ACK branch.
  //
  // NACK path signature: some proposer's ts > 1 — ts starts at 0, goes to 1
  //   on SendAckReq, and is incremented once per ProcessNack. ts > 1 is only
  //   reachable by processing at least one NACK.
  //
  // Run with: quint run --invariant ack_and_nack_reachable gwts_lattice_agreement.qnt --main gwts_standard
  val ack_and_nack_reachable =
    not (
      // ACK path: some acceptor raised its accepted_set (non-empty after ACKing)
      NODES.exists(p => choreo::s.system.get(p).accepted_set.size() > 0)
      // NACK path: some proposer incremented ts beyond the initial SendAckReq
      and NODES.exists(p => choreo::s.system.get(p).ts > 1)
    )

  // Witness: two proposers decide on different but comparable sets.
  //
  // n1 decides S1 = {2,5,11,15,22,24,28}
  // n4 decides S_all = {2,5,11,15,22,24,28,33}
  // lat_le(S1, S_all) = true  (S1 ⊆ S_all — comparable decisions ✓)
  //
  // Run with: quint run --invariant comparable_decisions_reachable gwts_lattice_agreement.qnt --main gwts_standard
  val comparable_decisions_reachable =
    not(NODES.exists(p => {
      val sp = choreo::s.system.get(p)
      NODES.exists(q => {
        val sq = choreo::s.system.get(q)
        sp.decided and sq.decided
          and sp.decided_set != sq.decided_set
          and lat_le(sp.decided_set, sq.decided_set)
      })
    }))

  // =========================================================================
  // TEST SCENARIOS
  // =========================================================================

  // T: Complete round 0 — n1 proposes, n2/n3/n4 ACK, n1 decides.
  //
  // Happy path (no NACKs):
  //   Phase 1: all 4 nodes disclose their batch values.
  //            n1 collects them (BRB threshold=3 met), builds proposed_set.
  //   Phase 2: n1 broadcasts AckReq with proposed_set and ts=1.
  //            n2/n3/n4 update their svs then each ACK (accepted_set=∅ ⊆ proposed_set).
  //            n1 sees byz_quorum=3 ACKs for the same accepted_set and decides.
  //
  // Expected final state: n1.decided = true,
  //   n1.decided_set = union of all four nodes' batch[0]
  //   (for the standard instance: {2,5} ∪ {11,15} ∪ {22,24,28} ∪ {33} = {2,5,11,15,22,24,28,33})
  run round0_complete_test =
    init
      // Phase 1: value disclosure
      .then(step_with("n1", do_broadcast_val))
      .then(step_with("n2", do_broadcast_val))
      .then(step_with("n3", do_broadcast_val))
      .then(step_with("n4", do_broadcast_val))
      // n1 collects vals (all 4 ValMsgs received → proposed_set = full union)
      .then(step_with("n1", do_collect_vals))
      .expect(s.system.get("n1").brb_ready.contains(0))
      .expect(lat_le(BATCH_VALUES.get("n1").get(0), s.system.get("n1").proposed_set))
      // Phase 2: n1 sends AckReq
      .then(step_with("n1", do_send_ack_req))
      .expect(s.system.get("n1").ack_req_sent)
      // Acceptors update svs so SAFEA passes, then ACK
      .then(step_with("n2", do_update_svs))
      .then(step_with("n3", do_update_svs))
      .then(step_with("n4", do_update_svs))
      .then(step_with("n2", do_respond_ack_req))
      .then(step_with("n3", do_respond_ack_req))
      .then(step_with("n4", do_respond_ack_req))
      // n1 updates its svs so SAFE passes on the incoming AckMsgs
      .then(step_with("n1", do_update_svs))
      // n1 decides (3 ACKs from n2/n3/n4 = byz_quorum)
      .then(step_with("n1", do_decide))
      .expect(
        s.system.get("n1").decided
          and s.system.get("n1").decided_set ==
            BATCH_VALUES.get("n1").get(0)
              .union(BATCH_VALUES.get("n2").get(0))
              .union(BATCH_VALUES.get("n3").get(0))
              .union(BATCH_VALUES.get("n4").get(0))
      )
}

// =============================================================================
// STANDARD INSTANCE
// n=4, f=1 (n ≥ 3f+1: 4 ≥ 4 ✓), MAX_ROUND=4
// Byzantine quorum: ⌊(4+1)/2⌋+1 = 3
// BRB threshold: 4-1 = 3
//
// Integers 1-40 are distributed across 4 nodes (10 per node), spread across
// 5 rounds (0-4) with varied batch sizes to exercise single- and multi-value
// proposals. Values are interleaved non-sequentially across nodes for realism.
//
//   round |    n1      |     n2      |     n3      |    n4
//   ------+------------+-------------+-------------+-----------
//     0   | {2, 5}     | {11, 15}    | {22, 24, 28}| {33}
//     1   | {9}        | {18, 13, 20}| {30}        | {39, 35, 31}
//     2   | {3, 7}     | {17}        | {25, 21}    | {37, 40}
//     3   | {1, 4}     | {12, 19}    | {27, 26}    | {34, 36}
//     4   | {8, 6, 10} | {14, 16}    | {23, 29}    | {38, 32}
//
// MAX_ROUND=4: all nodes have non-empty batches in every round.
// =============================================================================
module gwts_standard {
  import GWTSLatticeAgreement(
    N = 4,
    F = 1,
    NODES     = Set("n1", "n2", "n3", "n4"),
    BYZ_NODES = Set(),            // no Byzantine nodes — correct-only execution
    BYZ_VALUES = Set(),           // no fabricated values needed
    BATCH_VALUES = Map(
      "n1" -> Map(0 -> Set(2, 5),     1 -> Set(9),          2 -> Set(3, 7),     3 -> Set(1, 4),     4 -> Set(8, 6, 10)),
      "n2" -> Map(0 -> Set(11, 15),   1 -> Set(18, 13, 20), 2 -> Set(17),       3 -> Set(12, 19),   4 -> Set(14, 16)),
      "n3" -> Map(0 -> Set(22, 24, 28), 1 -> Set(30),       2 -> Set(25, 21),   3 -> Set(27, 26),   4 -> Set(23, 29)),
      "n4" -> Map(0 -> Set(33),       1 -> Set(39, 35, 31), 2 -> Set(37, 40),   3 -> Set(34, 36),   4 -> Set(38, 32)),
    ),
    MAX_ROUND = 4
  ).*
}

// =============================================================================
// BYZANTINE INSTANCE
// Same topology as gwts_standard; n4 is Byzantine (F=1 tolerance).
// BYZ_VALUES adds two fabricated integers in (INT32_MAX, UINT32_MAX] (i.e.
// outside the [1, 2^31-1] range for correct values), so E-validity filters
// can be exercised during simulation.
// =============================================================================
module gwts_byzantine {
  import GWTSLatticeAgreement(
    N = 4,
    F = 1,
    NODES      = Set("n1", "n2", "n3", "n4"),
    BYZ_NODES  = Set("n4"),                        // n4 behaves arbitrarily
    BYZ_VALUES = Set(2147483648, 4294967295),       // INT32_MAX+1, UINT32_MAX: outside E
    BATCH_VALUES = Map(
      "n1" -> Map(0 -> Set(2, 5),     1 -> Set(9),          2 -> Set(3, 7),     3 -> Set(1, 4),     4 -> Set(8, 6, 10)),
      "n2" -> Map(0 -> Set(11, 15),   1 -> Set(18, 13, 20), 2 -> Set(17),       3 -> Set(12, 19),   4 -> Set(14, 16)),
      "n3" -> Map(0 -> Set(22, 24, 28), 1 -> Set(30),       2 -> Set(25, 21),   3 -> Set(27, 26),   4 -> Set(23, 29)),
      "n4" -> Map(0 -> Set(33),       1 -> Set(39, 35, 31), 2 -> Set(37, 40),   3 -> Set(34, 36),   4 -> Set(38, 32)),
    ),
    MAX_ROUND = 4
  ).*
}
