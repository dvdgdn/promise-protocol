# 7) Domains & Templates

**Quick refresher:** a **Domain** = `(Namespace, Standard)` → `N/S`.  
- **Namespace** = a hierarchical path (e.g., `/coaching/sleep`).  
- **Standard** = a specific promise name starting with `_` (e.g., `/_twoSessionISIImprovement`).  
Each namespace usually has **multiple** standards (promises). ABDUCTIO and SPONSIO both reference these, but **either can run alone**.

---

## A) `/coaching/sleep` — realistic standards a sleep coach might promise

| Standard (S) | What it means (plain) | Key params (examples) |
|---|---|---|
| **_twoSessionISIImprovement** | Two sessions within a short window improve ISI by a set amount | `isi_delta≥6`, `window_days≤14` |
| **_sleepLatencyReduction** | Sleep-onset latency (SOL) drops by X minutes | `sol_delta_minutes≥20`, `window_days=14` |
| **_wakeAfterSleepReduction** | Wake-after-sleep-onset (WASO) drops by X minutes | `waso_delta_minutes≥20`, `window_days=14` |
| **_sleepEfficiencyIncrease** | Sleep efficiency improves by X percentage points | `se_delta_pct≥5`, `window_days=14` |
| **_twoSessionsWithinDays** | Delivery constraint for the program | `days≤14` |
| **_diaryAdherenceAtLeast** | Client logs enough diary entries | `rate≥0.85` |

**Example templates (how a coach actually uses them)**  
- *Template: “Two-Session Sleep Boost”*  
  - Domain paths used:  
    - `/coaching/sleep/_twoSessionsWithinDays{days:14}`  
    - `/coaching/sleep/_twoSessionISIImprovement{isi_delta:6, window_days:14}`  
    - `/coaching/sleep/_diaryAdherenceAtLeast{rate:0.85}`  
  - ABDUCTIO produces a pre-commit score *(Credence, Confidence)* for this claim.  
  - SPONSIO Earnest ties payment to the pre-registered pass rule.

- *Template: “Latency & WASO Combo”*  
  - Domain paths used:  
    - `/coaching/sleep/_sleepLatencyReduction{sol_delta_minutes:20, window_days:14}`  
    - `/coaching/sleep/_wakeAfterSleepReduction{waso_delta_minutes:20, window_days:14}`  
    - `/coaching/sleep/_diaryAdherenceAtLeast{rate:0.85}`

---

## B) `/coaching/habit_control/smoking` — more than one quit promise

| Standard (S) | What it means (plain) | Key params (examples) |
|---|---|---|
| **_ninetyDayAbstinence** | 90 consecutive nicotine-free days | `days:90`, `deadline:YYYY-MM-DD` |
| **_cotinineNegative** | Optional biochemical verification | `method:{urine,saliva}`, `threshold` |
| **_dailyCheckinAdherenceAtLeast** | Minimum check-in compliance | `rate≥0.85` |
| **_setQuitDateBy** | Define a quit date before starting | `date:YYYY-MM-DD` |
| **_relapseResetsStreak** | Rule that resets the counter on relapse | `enabled:true` |

**Example templates**  
- *Template: “90-Day Quit with Check-ins”*  
  - `/coaching/habit_control/smoking/_setQuitDateBy{date:2026-01-15}`  
  - `/coaching/habit_control/smoking/_ninetyDayAbstinence{days:90, deadline:2026-05-01}`  
  - `/coaching/habit_control/smoking/_dailyCheckinAdherenceAtLeast{rate:0.85}`  
  - `/coaching/habit_control/smoking/_relapseResetsStreak{enabled:true}`  
  - *(Optional)* `/coaching/habit_control/smoking/_cotinineNegative{method:"urine", threshold:"standard"}`

---

## C) `/entrepreneurship/viability` — realistic reviewer promises (jurisdiction via params)

| Standard (S) | What it means (plain) | Key params (examples) |
|---|---|---|
| **_opinionExport** | A signed viability opinion/export in the required format | `jurisdiction:"DE"`, `form_id:"GZ-04"` |
| **_assumptionLogComplete** | Key assumptions documented | `fields:["market_size","cac","margin"]` |
| **_breakevenForecast** | Breakeven months with uncertainty bands | `p50_months`, `p80_months` |
| **_liquidityPlanProvided** | Liquidity coverage horizon provided | `months≥12` |
| **_evidenceCitationsAttached** | Sources and exhibits attached | `min_count≥5` |
| **_reviewerSignature** | Qualified reviewer attests and signs | `issuer_role`, `expires_at` |
| **_followUpOutcomeRequested** | Outcome follow-up for calibration | `months∈{6,12}` |

**Example template (reviewer lane)**  
- *Template: “Viability Opinion (Jurisdictional Export)”*  
  - `/entrepreneurship/viability/_assumptionLogComplete{fields:["market_size","cac","margin"]}`  
  - `/entrepreneurship/viability/_breakevenForecast{p50_months:14, p80_months:18}`  
  - `/entrepreneurship/viability/_liquidityPlanProvided{months:12}`  
  - `/entrepreneurship/viability/_evidenceCitationsAttached{min_count:5}`  
  - `/entrepreneurship/viability/_opinionExport{jurisdiction:"DE", form_id:"GZ-04"}`  
  - `/entrepreneurship/viability/_reviewerSignature{issuer_role:"Steuerberater"}`  
  - *(Optional)* `/entrepreneurship/viability/_followUpOutcomeRequested{months:6}`

*Note:* The **namespace** is general (`/entrepreneurship/viability`); **jurisdiction** is a **parameter**. We don’t bake “de” into the namespace.

---

## D) `/services/web` — objective acceptance for small projects

| Standard (S) | What it means (plain) | Key params (examples) |
|---|---|---|
| **_pagespeedScoreAtLeast** | Performance threshold at launch | `mobile≥90`, `desktop≥90` |
| **_functionalContactForm** | Contact form works end-to-end | `status:"pass"` |
| **_deliversByDate** | Delivery deadline | `due:"2025-10-30"` |
| **_acceptanceTestSuitePass** | Agreed test suite passes | `suite_id:"TS-123"` |
| **_defectWarrantyWindowDays** | Post-launch fix window | `days:14` |

**Example template**  
- *Template: “Five-Page Launch with Guardrails”*  
  - `/services/web/_deliversByDate{due:"2025-10-30"}`  
  - `/services/web/_pagespeedScoreAtLeast{mobile:90, desktop:90}`  
  - `/services/web/_functionalContactForm{status:"pass"}`  
  - `/services/web/_acceptanceTestSuitePass{suite_id:"TS-123"}`  
  - `/services/web/_defectWarrantyWindowDays{days:14}`

---

## E) Cross-domain rails (reused everywhere)

| Namespace | Standard (S) | What it enforces |
|---|---|---|
| `/payments/timing` | **_authorizeCaptureRefund** | Money moves via PSP auth→capture/refund; no custody |
| `/verification` | **_evidenceExportProvided** | A one-page PDF/JSON decision export is produced |
| `/identity` | **_verifiedLevelAtLeast** | Higher-stakes actions require stronger ID (e.g., `kyc1`) |
| `/dispute` | **_neutralReviewWindowDays** | Time-boxed neutral review path (e.g., `days:7`) |

These are **standards** like any other; templates reference them to keep behavior consistent across domains.

---

## How promises reference domains (mapping)

> “We’ll improve your sleep by ≥6 ISI points within 14 days, across two sessions; else we don’t capture the success fee.”

**Maps to:**
- `/coaching/sleep/_twoSessionsWithinDays{days:14}`  
- `/coaching/sleep/_twoSessionISIImprovement{isi_delta:6, window_days:14}`  
- `/coaching/sleep/_diaryAdherenceAtLeast{rate:0.85}`  
- `/payments/timing/_authorizeCaptureRefund{window_days:7}`  
- `/verification/_evidenceExportProvided{format:["PDF","JSON"]}`

The **promise body** includes the domain paths and the **parameters**. ABDUCTIO can compute *(Credence, Confidence)* for this specific composition; SPONSIO can settle it if you enable Earnest.

---

## Discovery & governance (so this stays sane)
- The **Domain Registry** holds the approved namespaces and standards, their parameters, and examples.  
- **Experiments** can introduce new standards in any namespace.  
- A standard becomes a **domain “standard”** (capital S) after adoption by ≥3 independent users or a class vote—versioned as `_name_v2` when updated.  
- **Merit** accrues to authors of standards that get adopted and **hold up** in outcomes.

---

## Authoring checklist (add a domain in an afternoon)
1) Pick a realistic **namespace** (general area), e.g., `/coaching/anxiety_management`.  
2) Define **2–5 standards** (promise names starting with `_`) with clear pass rules and parameters.  
3) Draft **one template** that references a few of those standards + the cross-domain rails.  
4) Pilot 10–20 cases; keep the audit export identical to other domains.  
5) If results are good, submit to the registry as a standard and start earning merit.

**Bottom line:** Namespaces are the **places**; underscore standards are the **promises**. Multiple promises live in each place. ABDUCTIO and SPONSIO both speak this language—so your decisions are clear before you act, and your settlements are boring after you do.
