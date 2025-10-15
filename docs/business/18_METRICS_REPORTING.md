# 18) Metrics & Reporting

**Plain idea:** no vanity charts—just **receipts**. Every important action leaves a one-page artifact; every number on a dashboard is tied to those artifacts with a hash you can verify. Metrics are **domain-scoped**, **boat-scoped**, and **gate-driven**.

---

## North Star (two things we must grow)
1) **Pre-commit decisions made with justified confidence**  
   → Count of ABDUCTIO exports used in real decisions, plus their **calibration quality**.
2) **Post-commit promises settled on outcomes**  
   → Count of SPONSIO decisions (KEPT/NOT KEPT) with **auto-decision %** and **dispute %**.

If these rise with quality, the snowball is rolling.

---

## Public Scoreboard (what anyone can see)

We publish a **Metrics Page** with **per-domain** and **per-boat** stats, updated weekly. Every figure shows:
- **Definition** (plain language + formula),
- **Window & sample size** (n),
- **Wilson lower bound** for rates,
- **Template/standard versions** in force.

### Public KPIs (with targets / gates)

| Area | KPI | Definition (plain) | Target | Gate (red) |
|---|---|---|---:|---:|
| ABDUCTIO | **Acceptance %** | % of reviewer exports accepted by recipients on first pass or trivial edits | ≥ 80% | < 65% |
| ABDUCTIO | **Prep time (median)** | Reviewer minutes from intake to signed export | ≤ 90 min | > 120 min |
| ABDUCTIO | **Calibration (Brier)** | Avg. squared error of Credence vs later outcome (when available) | ↓ over time | flat/worse 2 qtrs |
| Earnest | **Auto-decision %** | % of promises that resolve without human review | ≥ 90% | < 80% |
| Earnest | **Disputes %** | % of promises entering dispute window | ≤ 3% | > 5% |
| Earnest | **Capture/refund latency** | Median time from outcome to money move | ≤ 2 h | > 24 h |
| Virtual | **Voucher funding %** | % ABDUCTIO exports redeemed via Report Passes | ≥ 60% | < 30% |
| Virtual | **Money-confusion %** | Support tickets mistaking vouchers for money | < 2% | ≥ 5% |
| Platform | **Export failure %** | Missing/invalid decision exports | < 1% | ≥ 2% |
| Platform | **Time-to-cash** | Days from client commit to platform revenue recognition | < 30 d | > 45 d |

> **Wilson bound:** We display the **lower 95% CI** for any rate to avoid over-claiming on small n.

---

## Internal Operating Metrics (we run the fleet by these)

### A) ABDUCTIO (pre-commit)

- **Exports / day (by domain)**
- **Acceptance % (by recipient type)**  
- **Prep time quantiles (50/75/90th)**
- **Calibration suite** (on cohorts with follow-ups):
  - **Brier score:** `mean( (p − y)^2 )` where `p=Credence`, `y∈{0,1}`  
  - **Log score:** `−mean( y·ln p + (1−y)·ln(1−p) )`  
  - **Confidence coverage:** % of claims where the confidence band bracketed the outcome  
  - **Reliability diagram** buckets (deciles of Credence)
- **Stopping-rule adherence:** % reports with “enough for stakes” achieved (no unnecessary steps)
- **Top objection categories** from recipients (to tighten templates)

### B) SPONSIO Earnest (post-commit)

- **Promises / day (by template)**
- **Kept-rate** (with case-mix & Wilson lower bound)
- **Auto-decision %, Dispute %, Reverse-on-appeal %**
- **Adherence met %** (e.g., ≥6/7 diary entries)
- **Outcome latency** (from window end → decision)
- **Payments health:** auth aging, capture/refund latency, webhook success %, reconciliation diffs
- **Support minutes (median/95th)** and **top ticket reasons**

### C) SPONSIO Virtual

- **Vouchers: sold, redeemed, outstanding**
- **% exports funded by vouchers** (weekly)
- **Confusion tickets %** (money-language)
- **LNE counter** (12-mo rolling volume vs thresholds)

### D) Domain Scores & Merit (quality signals)

- **DomainScore** per agent (Wilson lower bound w/ recency weighting)
- **Merit events** (adoptions × quality × decay), domain leaderboards
- **Template version fitness** (kept-rate vs prior, adjusted for difficulty)

### E) Financial / Growth

- **Contribution per export / per promise** (rolling)
- **CAC / payback** (reviewer vs coach lanes)
- **Time-to-cash** (order → revenue recognized)
- **Refund ratio** and **chargeback ratio**
- **Fleet P&L** by boat (contribution → fixed)

---

## Dashboards & Cadence

- **Daily Ops (internal):** auto-decision %, export failures, webhook health, support median, auth aging.
- **Bi-weekly Gate Review (internal):** four stoplights per boat—**Technical, Legal, Market, Economics**—with a one-change plan. Two Yellows in a row or any Red → **pause intake** for that boat.
- **Monthly Member Report (public):** KPIs, case briefs, template changes, bounty awards, merit snapshots.
- **Quarterly Transparency (public):** calibration charts, domain score distributions, dispute post-mortems, governance votes.

---

## Data Lineage & Auditability

- **Event log (append-only):** every intake, evidence item, decision, export, and money move emits a signed event with a **content hash**.  
- **Decision Export:** carries hashes of evidence, rule evaluated, and signer; the public QR verifies the same summary server-side.  
- **Reproducibility:** ABDUCTIO stores model version, prompt, seeds, inputs; Earnest stores template version + rule parameters.  
- **Change control:** any metric definition change is a PR to the **metrics spec**; dashboards pull from versioned views.

---

## Publishing Rules (no cherry-picking)

- **Minimum n** before showing a rate: **n ≥ 30**; otherwise “collecting data” badge.  
- **Always show n and Wilson bounds** next to a rate.  
- **No rank-ordering providers** outside a domain; no cross-domain reputation.  
- **Template version pinned** on any historical chart (we don’t mix v1 and v2 performance).  
- **Case-mix disclosure** (e.g., baseline ISI distribution) for fairness.

---

## Alerts & Kill-Switches (auto)

- **Export failure ≥ 2% (24h)** → page on-call; stop new starts until fixed.  
- **Auto-decision < 80% (7d)** → pause boat; simplify pass rule (medians, clearer adherence).  
- **Disputes > 5% (14d)** → pause intake; run audit; adjust template/eligibility.  
- **Voucher confusion ≥ 5% (7d)** → freeze voucher sales; relabel; narrow catalog.  
- **Custody/“escrow” term detected** in UI/emails → kill-switch; legal review.  
- **Reconciliation diffs > €X or >0.5%** → freeze captures; panic-refund tool available.

All alerts annotate the Metrics Page with **“Paused for quality”** banners and a short reason.

---

## Metric Definitions (plain language + formula snippets)

- **Kept-rate (domain / template):**  
  `KEPT / (KEPT + NOT KEPT)` with **Wilson 95%** lower bound shown.
- **Auto-decision %:**  
  `Auto decisions / All decisions`. “Auto” = no human override.
- **Disputes %:**  
  `Disputes opened / All decisions`.
- **Acceptance % (ABDUCTIO):**  
  `Accepted (first pass or trivial edits) / All submitted`.
- **Brier score:**  
  `mean( (Credence − Outcome)^2 )`, lower is better.
- **Log score:**  
  `−mean( y·ln p + (1−y)·ln(1−p) )`, lower is better.
- **Confidence coverage:**  
  % where the confidence band captured the realized outcome.
- **Contribution (export):**  
  `Revenue_per_export − (infra + support_var)`.
- **Contribution EV (promise):**  
  `Kept_rate × margin_kept + (1−Kept_rate) × margin_not_kept`.

The **metrics spec** repo holds these with SQL views/tests.

---

## Privacy in Reporting

- **Aggregate by default;** no PII on public pages.  
- **Redaction by design** in exports; hashes only.  
- **Small-n suppression** for any slice that risks re-identification.  
- **Special-category data** never leaves private aggregates; consent gates on any share.

---

## How Metrics Improve the System (feedback loops)

- **ABDUCTIO ⟶ Earnest:** when disputes rise, we tighten pre-commit expectations (eligibility, instruments, medians).  
- **Earnest ⟶ ABDUCTIO:** outcome labels feed calibration; credence/confidence get sharper per domain and template version.  
- **Merit ⟶ Friction:** high-merit actors face lighter evidence and smaller holds; low-merit face stricter checks—published policy with numbers.

---

## What We’ll Add Later (once we have data)

- **Difficulty-adjusted kept-rate** (case-mix model), not raw averages.  
- **Per-recipient acceptance model** for viability (learn what each office cares about).  
- **Rater calibration charts** (who is reliably strict/lenient by domain).  
- **Post-resolution NPS** for both parties, tied to the decision export (opt-in).

---

## The Promise About Our Numbers

1) Every public metric links to **how we compute it**.  
2) Every rate shows its **sample size and confidence bound**.  
3) Any major drop triggers a **pause and a fix**, not a PR spin.  
4) If you doubt a number, you can **click the QR on a random export** and see the exact rule, evidence hash, and timestamp we decided on.

**Bottom line:** metrics aren’t decoration here—they’re part of the protocol. If we can’t measure it, we don’t promise it. And if we promise it, you can check the math.
