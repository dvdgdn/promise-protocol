# 13) Validation Plan

**Plain idea:** we don’t “launch and pray.” We **stage-gate** each boat (ABDUCTIO—Viability, SPONSIO Earnest—Sleep, SPONSIO Virtual—Report Passes) with small, auditable trials. If a gate fails twice, we pause, fix one thing, and re-run a micro-pilot.

---

## What we must learn (before we scale)

1) **ABDUCTIO works alone:** a first-time reader can act on *(Credence, Confidence)*; reviewer exports are accepted with minimal rework.  
2) **Earnest is boring:** outcomes auto-resolve; disputes are rare; money moves exactly when the rule says (no custody).  
3) **Virtual is clean:** vouchers are clearly **issuer-only** and fund ABDUCTIO without “this is money” confusion.  
4) **Economics hold:** contribution margin is positive; CAC is sensible; ops load is small.  
5) **Compliance holds:** copy and flows match our legal posture (payment timing; closed-loop vouchers; privacy by design).

---

## Staged validation (by boat)

### A) ABDUCTIO — Viability (Reviewer lane)
**Hypotheses**
- H1: A one-page *(Credence, Confidence)* + structured export cuts prep time to **≤ 90 min** (median).  
- H2: **≥ 80%** of exports are accepted by recipients (first submission or minor edits).  
- H3: Founders and recipients understand the export without a call.

**Design**
- **Sample:** 10–20 dossiers (Weeks 3–4), then 30–60 more (Weeks 5–10).  
- **Measures:** prep time, acceptance/objections, recipient questions, NPS for reviewers/founders, % of exports generated without manual formatting.  
- **Artifacts:** export PDF/JSON; reviewer signature; short “acceptance log.”

**Gates (Go/No-Go)**
- **Green:** acceptance ≥ 80%; prep time ≤ 90 min (median); < 20% need rework; ≥ 70% founders rate clarity ≥ 4/5.  
- **Yellow:** acceptance 65–79% or prep 90–120 min; rework 20–35%.  
- **Red:** acceptance < 65% or prep > 120 min.

**If Yellow/Red:** tighten the export checklist (assumptions, evidence), improve template copy, add a “recipient view” summary; re-run **10-case** micro-pilot before more intake.

**Calibration (longer-cycle)**
- **Follow-ups at 6/12 months:** collect outcome snapshots to calibrate ABDUCTIO *(Credence, Confidence)* using **Brier/log score** and reliability plots. (Does not block MVP scale, but starts early.)

---

### B) SPONSIO Earnest — Sleep
**Hypotheses**
- H1: Auto-decisions handle **≥ 90%** of cases (no manual judgment).  
- H2: Disputes are **≤ 3%** with the chosen instruments (ISI + diary, median windows, adherence rule).  
- H3: Coaches see **higher conversion** vs their baseline because risk is fair (“authorize now; capture on KEPT”).

**Design**
- **Sample:** 20–30 promises (Weeks 3–4), then 30–70 more (Weeks 5–10).  
- **Pass rules:** Path A (ISI −≥ 6) or Path B (SOL & WASO −≥ 20 min), 14-day window; adherence ≥ 6/7 diaries/week.  
- **Measures:** kept-rate, auto-decision %, disputes %, median support minutes/ticket, conversion uplift for coaches, refund/capture timings.

**Gates (Go/No-Go)**
- **Green:** auto-decision ≥ 90%; disputes ≤ 3%; median support ≤ 20 min; no custody incidents; coaches opt-in ≥ 60% after first run.  
- **Yellow:** auto-decision 80–89% or disputes 3–5% or support 20–35 min.  
- **Red:** auto-decision < 80% or disputes > 5% or any sign of custody/“escrow” language.

**If Yellow/Red:** switch to **7-day median** aggregates (not best night), tighten eligibility (exclude travel/med changes), adjust threshold ranges, add a clearer adherence walkthrough; re-pilot **15** cases.

**Payments reality check**
- If authorization windows are tight, use **capture + auto-refund** for the success component. Verify webhook idempotency and reconciliation.

---

### C) SPONSIO Virtual — Report Passes (closed loop)
**Hypotheses**
- H1: Report Passes fund ABDUCTIO without user confusion: **< 2%** of support tickets misinterpret vouchers as “money.”  
- H2: Founders actually use them: **≥ 60%** of ABDUCTIO exports are funded by passes by Week 12.

**Design**
- **Launch Weeks 7–8:** start with a single catalog item—**viability exports only**.  
- **Measures:** redemption rate, % ABDUCTIO funded by passes, support tickets about “money,” LNE **threshold counter**.

**Gates (Go/No-Go)**
- **Green:** ≥ 60% funded by passes; confusion tickets < 2%; counter below alert threshold.  
- **Yellow:** 30–59% funded or 2–4% confusion.  
- **Red:** confusion ≥ 5% or catalog creep beyond ABDUCTIO.

**If Yellow/Red:** narrow catalog, relabel (“issuer-only Report Pass”), add an inline explainer, publish a FAQ; re-check for two weeks.

---

## Cross-cutting gates (apply to every boat)

| Gate | Metric | Green | Yellow | Red |
|---|---|---|---|---|
| **Technical** | Decision auto-resolution | ≥ 90% | 80–89% | < 80% |
|  | Export failures | < 1% | 1–2% | > 2% |
| **Legal** | Custody/“escrow” risk | none | copy confusion | any custody |
|  | Voucher posture | issuer-only; LNE counter ok | minor confusion | P2P/cash-out seen |
| **Market** | Acceptance (ABDUCTIO) | ≥ 80% | 65–79% | < 65% |
|  | Disputes (Earnest) | ≤ 3% | 3–5% | > 5% |
| **Economics** | Contribution margin | positive | breakeven-ish | negative |
|  | CAC vs 6-mo GM | < ⅓ | ⅓–½ | > ½ |
|  | Time-to-cash | < 30 d | 30–45 d | > 45 d |
| **Ops** | Support (median) | ≤ 20 min | 20–35 min | > 35 min |

**Rule:** two consecutive Yellows on the same metric = a pause; any Red = immediate pause and micro-pilot after a fix.

---

## Experiments we’ll run (fast, controlled)

- **Evidence aggregation:** median vs mean vs trimmed mean (sleep).  
- **Threshold tuning:** ISI −6 vs −5 with stricter adherence.  
- **Fee mix:** base vs success component split (coach conversion vs disputes).  
- **Copy tests:** “authorize now; capture on kept” vs longer copy; voucher label variants (“Report Pass” vs “Voucher for ABDUCTIO”).  
- **ABDUCTIO stopping rule UI:** show “value of more info” nudges vs silence.

Each test runs until **95%** confidence on the primary metric or 2 weeks—whichever first. We stop tests that worsen disputes or add legal risk.

---

## Instrumentation (what we log by default)

- **Per promise/export:** template version, parameters, identity level, evidence counts, adherence, pass rule chosen, Decision result, export hash.  
- **Payments:** PSP IDs, auth/capture/refund status, latencies (no PANs).  
- **Support:** ticket category, minutes spent, resolution outcome.  
- **Reputation:** per-domain **DomainScore** (Wilson bound + recency).  
- **ABDUCTIO calibration:** predicted vs observed (where follow-ups exist); **Brier/log score**.

---

## Decision cadence (every two weeks)

- **Gate Review:** one slide per boat (tech/legal/market/econ stoplights).  
- **One-Change Rule:** choose **one** change per boat; ship within 7 days; re-measure.  
- **Freeze Power:** any gate owner can freeze new intake on their boat; unfreeze requires two green check-ins.

---

## Kill-switch triggers (automatic)

- Any sign of **fund custody** in code or copy → freeze Earnest boat, hotfix, external audit.  
- Voucher confusion ≥ **5%** of tickets over 7 days → freeze sales, relabel, limit catalog.  
- Disputes > **5%** for 14 days → stop intake, tighten instruments/eligibility, re-pilot.  
- Export failure > **2%** → roll back to prior TemplateVersion; root-cause before relaunch.

---

## Success by Week 12 (what “ready to scale” means)

- **ABDUCTIO—Viability:** acceptance ≥ 80%; prep ≤ 90 min (median); ≥ 50 signed exports; recipient questions trending down; 6-month follow-ups scheduled ≥ 40%.  
- **Earnest—Sleep:** 80–120 promises total; auto-decision ≥ 90%; disputes ≤ 3%; coach opt-in ≥ 60%; conversion ↑ vs baseline.  
- **Virtual:** ≥ 60% of ABDUCTIO exports funded by Report Passes; confusion < 2%; LNE counter well below alert.  
- **Economics:** positive contribution margins on both boats; CAC < ⅓ of 6-mo gross margin; time-to-cash < 30 days.  
- **Compliance:** DPIA/ROPA/LIAs done; copy reviewed; T&Cs live; incident drills passed.

If all green for **two consecutive bi-weekly reviews**, plan the next adjacent domain (e.g., `/coaching/habit_control/smoking` or `/services/web`) using the same rails and gates.

**Bottom line:** tiny, honest experiments → simple, public gates → scale only when the data says “go.” That’s how we keep the promises we make about keeping promises.
