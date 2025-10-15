# 16) Risks & Mitigations

**Plain idea:** we assume things go wrong. We design for it with **gates, kill-switches, and tiny, auditable loops**. Each risk has an owner, a metric, and a playbook.

---

## A. Summary table (read this first)

| Risk area | What can go wrong | Early signal | Mitigation (playbook) |
|---|---|---|---|
| **Product–Market Fit** | We try to do two mediocre things; no one loves either | Low conversion; poor NPS; churn | **Gated boats**, WIP limit (max 2 in build/scale), bi-weekly gate review; pause boat after 2× yellow or any red |
| **Legal posture** | Custody/“escrow” creep; vouchers look like money; health claims | Support tickets with wrong words; regulator questions | Earnest = **payment timing** only; Virtual = **issuer-only** vouchers; medical-claims linting; copy freeze + relabel; counsel check before unpausing |
| **Payments** | PSP auth expires; webhook drops; chargebacks | Stuck auths; reconciliation drift; dispute spikes | **Capture+auto-refund** pattern for long windows; **idempotent webhooks**; nightly reconciliation; clear decision exports for chargebacks |
| **Evidence quality** | Instruments gamed; “best-night” screenshots | Outcome variance; suspicious clusters | Use **7-day medians**, adherence rules, random **audits**, optional lab checks, witness attest; auto-flag repeated pairs |
| **ABDUCTIO accuracy** | LLM hallucinations; overconfident credence; stale priors | Calibration gap (Brier/log score); user distrust | **Model/version pinning**, rationale traces, multi-pass cross-checks, **stopping rule** UI, follow-up calibration, human spot-checks on high-stakes |
| **Gaming & Sybils** | Fake clients, collusive coaches/raters; merit farming | Unusual cluster networks; fast merit jumps | **Merit ≠ money**, closed-loop **Report Passes**, identity tiers, Wilson bounds + recency, cross-camp agreement weighting, stake/hold sizing by merit |
| **Privacy & Security** | PII over-collection; breach; special-data mishandling | DPIA gaps; access anomalies | PII minimization; EU hosting; role-based access; redaction with hash trail; breach runbook (72h) |
| **Ops load** | Support minutes explode; decisions become manual | Median support > 20–30 min; export failures > 1% | Template hardening; self-serve guides; export regression tests; **pause intake** if SLOs missed |
| **Economics** | Negative contribution; CAC too high; slow cash | Margin slip; CAC/GM > ⅓; time-to-cash > 30d | Price/mix tweaks; reduce support; partner-led acquisition; throttle spend until two green months |
| **Reputation** | One loud failure poisons the well | Social spikes; refund threads | Fast, transparent **decision exports**; good-will refunds; post-mortem + template fix; publish metrics page |
| **Partner dependency** | PSP outage; reviewer drop-off | Error rates; throughput dips | Multi-PSP plan; retry/backoff; keep small reviewer bench; export offline queue |

---

## B. Product & market risks

### 1) Two mediocre things vs one loved thing
- **Risk:** splitting focus across ABDUCTIO and Earnest dilutes quality.  
- **Mitigation:** **gated fleet**. Each boat must pass **technical, legal, market, economics** gates two months running before scale. WIP limit = **2 boats**.

### 2) Inertia among reviewers/coaches
- **Risk:** switching costs; “our way works.”  
- **Mitigation:** white-label exports, 90-minute prep promise, partner pages, case briefs; start with **champions**, not consensus.

---

## C. Legal & compliance risks

### 3) Custody / “Escrow” by accident
- **Risk:** a flow, label, or email implies custody.  
- **Signals:** support tickets say “escrow”; copy drift.  
- **Mitigation:** code & copy linting for banned terms; **payment-timing** language only; flows = **authorize→capture/refund**; legal **kill-switch** pauses boat on any red.

### 4) Vouchers look like money (Virtual)
- **Risk:** vouchers perceived as e-money.  
- **Signals:** “cash-out?” tickets; off-platform trading attempts.  
- **Mitigation:** **issuer-only**, **no cash-out/P2P**, narrow catalog (**ABDUCTIO exports**), visible **LNE counter**; relabel to “Report Pass,” FAQ inline.

### 5) Health/medical claims creep
- **Risk:** “cure/treat” language triggers HWG/UWG issues.  
- **Mitigation:** measurable-improvement framing; coaching language; template copy reviews; yank any offending template version immediately.

---

## D. Payments & financial ops

### 6) Authorization window too short
- **Risk:** program > auth window.  
- **Mitigation:** **capture+auto-refund** success component; staged holds where permitted; explicit timelines in template.

### 7) Webhooks & reconciliation
- **Risk:** double captures, lost refunds.  
- **Mitigation:** **idempotency keys**, durable queue; nightly reconciliation job; alerting on mismatches; manual “panic refund” tool with audit.

### 8) Chargebacks
- **Risk:** client disputes despite clear rules.  
- **Mitigation:** one-page **decision export** with timestamps; adherence logs; quick merchant responses; prefer mediation over fights.

---

## E. Evidence & measurement risks

### 9) Instrument gaming & cherry-picking
- **Risk:** clients or providers cherry-pick data.  
- **Mitigation:** **median over 7-day windows**, adherence thresholds, exclude travel/med changes; random **audits**; difficulty weights and case-mix reporting.

### 10) Weak or biased measures
- **Risk:** scale/device misfit; wearables over-trusted.  
- **Mitigation:** **structured-subjective** first (ISI & diaries), devices as **supporting**, not decisive; validate instruments per domain; publish limitations.

---

## F. ABDUCTIO model risks

### 11) Hallucination, overconfidence, staleness
- **Signals:** calibration gap (Brier/log), reviewer overrides frequent.  
- **Mitigation:** pin **model versions**, store prompts/params; multi-pass cross-checks; rationale traces; **human spot-checks** for high-stakes; **follow-up calibration** feeds next priors.

### 12) Over- or under-investigation
- **Risk:** waste time or stop too soon.  
- **Mitigation:** **stopping rule** UX with value-of-information estimate; templates specify “enough for these stakes.”

---

## G. Gaming & integrity risks

### 13) Sybils & collusion (coach–client or rater rings)
- **Mitigation:** domain-scoped reputation; **Merit not money**; identity tiers for high-stakes; repeated-pair down-weighting; cross-camp agreement boosting; randomized audits; optional third-party tests (e.g., cotinine).

### 14) Goodhart’s Law (optimize the metric, not the outcome)
- **Mitigation:** rotate/ensemble metrics (e.g., ISI **and** diary); publish case-mix; introduce **difficulty weights**; Wilson lower bounds & recency; periodic template re-baselining.

---

## H. Privacy & security

### 15) PII and special-category data
- **Mitigation:** minimization; separate evidence store; encryption; access controls; **redaction with hash trail**; DPIA/ROPA; 72-hour breach process; sub-processor DPAs.

### 16) Linkage attacks via public exports
- **Mitigation:** redact PII by default; publish aggregates; QR verifies hashes without exposing raw evidence; consent gates for sharing.

---

## I. Ops & scalability

### 17) Support overload / manual decisions
- **Signals:** support median > 20–30 min; auto-decision < 90%.  
- **Mitigation:** template simplification; in-product guidance; dispute micro-flow with SLA; **pause intake** until SLOs green.

### 18) Reviewer bottlenecks
- **Mitigation:** partner bench; async queues; pay-for-speed option; clear acceptance checklists; Virtual **Report Passes** to smooth demand.

---

## J. Reputation & comms

### 19) Public blow-ups (real or misframed)
- **Mitigation:** publish **metrics page**; fast, factual post-mortems with decision exports; good-will refunds; dedicated comms runbook.

### 20) “This is gambling/escrow/crypto”
- **Mitigation:** consistent language (payment timing; issuer-only passes); no custody; no transferable credits; no event markets; a simple “How it works” diagram everywhere.

---

## K. Strategic & competitive

### 21) Copycats / platform giants
- **Mitigation:** **open protocol** (AGPL/CC0) + co-op moat (patronage/merit); domain-scoped trust data + decision exports are sticky; focus on **boring excellence** where giants prefer ads.

### 22) Over-expansion into weak domains
- **Mitigation:** **adjacent only**, template-first pilots, gate to scale; sunset underperforming domains fast.

---

## L. Kill-switches (automatic stops)

- **Custody detected or “escrow” copy live:** freeze Earnest boat; hot-fix; external audit.  
- **Voucher confusion ≥ 5% of tickets (7d):** freeze voucher sales; relabel; narrow catalog; resume < 2%.  
- **Disputes > 5% (14d):** stop intake; tighten instruments/eligibility; re-pilot 10–20 cases.  
- **Export failure > 2%:** roll back TemplateVersion; fix tests; relaunch.  
- **Auto-decision < 80%:** pause; simplify pass rule; require medians; resume after two green weeks.  
- **Data incident:** incident plan; notify within 72h; public post-mortem.

---

## M. Who watches what (owners & dashboards)

- **Legal owner:** copy linter hits, voucher counter, incident log.  
- **Payments owner:** auth aging, webhook success, reconciliation diffs.  
- **Evidence owner:** adherence %, audit queue, flagged clusters.  
- **ABDUCTIO owner:** calibration (Brier/log), override rate, model version map.  
- **Ops owner:** support median/95th, export failure %, dispute SLA.  
- **Finance owner:** contribution per lane, CAC/payback, time-to-cash.

Weekly 30-minute **Gate Review**: one slide per boat with **tech/legal/market/econ** stoplights; **one-change rule** for the next sprint.

---

**Bottom line:** we don’t eliminate risk—we **bound** it. Small boats, hard gates, fast pauses, and receipts (decision exports) keep errors cheap and trust intact. If something breaks, it breaks **small**, and we can show exactly how we fixed it.
