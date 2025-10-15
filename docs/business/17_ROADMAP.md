# 17) Roadmap

**Principle:** build the **gated snowball fleet**—small boats, hard gates, public receipts. ABDUCTIO and SPONSIO grow **in parallel** but **independently**; they click together through domains, instruments, identity, and exports.

---

## Phase 0 — Dockyard Ready (Weeks 0–2)
**Goal:** ship the rails once; reuse everywhere.

**Deliverables**
- Domain Registry (MVP): `/entrepreneurship/viability`, `/coaching/sleep` + cross-domain rails (`/verification`, `/payments/timing`, `/identity`).
- Decision Export (1-page PDF/JSON; hash & signer).
- ABDUCTIO Engine v0 (credence, confidence, rationale trace).
- Earnest payments adapter (authorize → capture/refund; idempotent webhooks).
- Evidence kit v0 (ISI + sleep diary; nicotine check-ins scaffold).
- Legal packet v0.9 (ToS, Privacy, DPA, DPIA draft; voucher T&Cs; copy lint rules).

**Gate to proceed**
- **Technical:** end-to-end sandbox auto-decision; export renders identically.
- **Legal:** counsel sign-off: no custody, closed-loop vouchers posture, health-claims guardrails.

---

## Phase 1 — Two Boats in Water (Weeks 3–12)
**Boat A: ABDUCTIO—Viability**  
**Boat B: SPONSIO Earnest—Sleep**  
(+ **Virtual Report Passes** to fund ABDUCTIO)

**Milestones**
- 10–20 live cases per boat → template tighten → 50–100 cases.
- Proof Pages + 3 Case Briefs (public receipts).
- Virtual vouchers live (issuer-only; viability exports catalog).

**Green gates to “Scale”**
- **ABDUCTIO:** acceptance ≥ 80%; reviewer prep ≤ 90 min (median).
- **Earnest (Sleep):** auto-decision ≥ 90%; disputes ≤ 3%; coach opt-in ≥ 60%.
- **Virtual:** ≥ 60% of ABDUCTIO funded by Report Passes; confusion < 2%.
- **Economics:** positive contribution per boat; time-to-cash < 30 days.

**If any gate goes yellow/red:** pause that boat, fix one thing, micro-pilot 10–20, retest.

---

## Phase 2 — Scale What Works, No New Boats (Months 4–6)
**Objective:** deepen two lanes before adding a third.

**Deliverables**
- ABDUCTIO v1: calibration loop (Brier/log score), “value-of-information” stopping rule UX.
- Sleep template v2: median windows, refined eligibility; optional wearable as **supporting** evidence.
- Viability export v2: recipient summary page; jurisdiction parameterization.
- PSP redundancy; nightly reconciliation & panic-refund tool.
- Merit v1: domain-scoped, decay, public leaderboard (non-monetary).

**Operating targets**
- Support median ≤ 20 min; export failure < 1%; voucher catalog still **ABDUCTIO-only**.

**Gate to proceed**
- Two consecutive green monthly reviews on **technical, legal, market, economics** for both boats.

---

## Phase 3 — One Adjacent Boat (Months 6–9)
**Pick one (data-driven):**
- **C) `/coaching/habit_control/smoking`** with `_ninetyDayAbstinence` + optional cotinine; or
- **C) `/services/web`** with `_pagespeedScoreAtLeast` + `_acceptanceTestSuitePass`.

**Deliverables**
- New domain standards (2–5 underscores) + one template v1.
- Evidence instrument(s) & export fields reused.
- Coach/freelancer partners (10–15) onboarded; 30–60 cases.

**Green gates to keep scaling the new boat**
- Auto-decision ≥ 90%; disputes ≤ 3%; contribution ≥ breakeven; legal posture unchanged (no custody; no token vibes).

**WIP limit remains 2 boats in build/scale.** If C enters “build,” one earlier boat must be in “scale/steady” (green twice).

---

## Phase 4 — Product Hardening & Transparency (Months 9–12)
**Deliverables**
- Public Metrics Page v1 (kept-rate, acceptance, auto-decision, disputes, contribution by boat).
- Reviewer sealing: viability exports as **Verifiable Credentials** (QR verify).
- Dispute micro-arbitration SLA (≤ 7 days) + credit-note rules.
- Identity `kyc1` enforced for signers & capturers.
- Governance cadence: first two GA votes on minor standards; bounty program live.

**Gate to proceed (org-level)**
- Contribution margin ≥ 0 for the fleet; CAC < ⅓ of 6-mo gross margin; time-to-cash < 30 d; no red legal flags for ≥ 60 days.

---

## Phase 5 — Horizontal Template Factory (Year 2, H1)
**Objective:** add surface area through templating, not heavy engineering.

**Deliverables**
- Template authoring kit (lint + test runner + preview exports).
- Domain expansion pack: 3–5 new templates across 2 existing namespaces (e.g., long-haul sleep program; “launch & index” for web).
- Merit v1.5: quality multipliers (kept-rate adjusted for difficulty; Wilson lower bounds).
- Localization pass (DE/EN UI copy; export i18n).

**Gate to proceed**
- New templates hit the same **green gates** before joining “standard” list.

---

## Phase 6 — Compliance Lift (Optional, Year 2, H2+)
**Only if we choose the “Core” path with a licensed partner.**

**Exploration track (no code without counsel)**
- EMI/PI partner RfI; safeguarding design; capital & audit implications.
- Sandbox: **stake-sized holds** simulated via Earnest; slashing semantics tested as **non-monetary** minus points (Merit) first.
- Legal greenlight before any stored-value unit.

**Alternative track (likely):** keep compounding Earnest + ABDUCTIO + Virtual; avoid stored value entirely.

---

## Always-On Tracks (run across phases)

**A. Reliability & Ops**
- SLOs: export failure < 1%; webhook success > 99.5%; support ≤ 20 min median.
- Kill-switches: custody hint, voucher confusion ≥ 5%, disputes > 5% → auto-pause boat.

**B. Security & Privacy**
- EU hosting; encryption in transit/at rest; role-based access; erasure/redaction with hash trail.
- DPIA/ROPA maintenance; 72-hour incident drills.

**C. Governance & Co-op**
- Quarterly merit reports; concurrent-majority votes for core changes; transparent bounty awards.
- Investor charter enforced (no control; capped returns) if any investment boat exists.

---

## What We Won’t Do (until a gate is green)
- No custody / “escrow” UX.  
- No transferable or cash-redeemable credits.  
- No medical/healing claims.  
- No >2 boats in build/scale at once.  
- No scale on manual decisions.

---

## The one-screen timeline (text)

```
0–2 w : Dockyard ready (rails, legal v0.9) ── GO gate
3–12 w : Boat A (ABDUCTIO–Viability) + Boat B (Earnest–Sleep) + Virtual vouchers
M4–6 : Scale A & B; Merit v1; PSP redundancy; calibration loop ── 2× Green gate
M6–9 : Add Boat C (Smoking OR Web) ── Green gate per boat
M9–12 : Transparency v1; VC sealing; GA votes; steady ops ── Fleet green gate
Y2 H1 : Template factory; domain expansion; Merit v1.5; i18n
Y2 H2+ : (Optional) Core path exploration with licensed partner; otherwise deepen lanes
```


**Bottom line:** a roadmap that compounds trust by *earning* it—one boat, one gate, one clean receipt at a time. If a gate isn’t green, the boat doesn’t grow. If it is, we don’t need permission—just the protocol.
