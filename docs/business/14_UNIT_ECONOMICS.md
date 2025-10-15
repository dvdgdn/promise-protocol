# 14) Unit Economics & Financials

**Plain idea:** skeptic-friendly math, not fairy dust. We show **per-case contribution**, **break-even volumes**, a **12-month ramp** you can sanity-check, and the **sensitivity levers** that really move the model. All numbers below are **illustrative, conservative defaults** you can overwrite in the spreadsheet.

---

## A) Assumptions (you can change these)

### Shared rails
- PSP fee (merchant side, borne by provider): **2.2% + €0.25** on captured charges.  
- PSP fee (on our platform fee transfer): **2.2% + €0.25** *(we model this—tiny but real)*.  
- Support cost of time: **€30/h** (loaded).  
- Infra per decision/export: **€3** (compute, storage, PDF/JSON).  
- Disputes target (Earnest): **≤ 3%**; auto-decision target: **≥ 90%**.

### ABDUCTIO (viability exports)
- Price (pay-as-you-go): **€59/export**.  
- Plan: **€199/mo** up to **6** exports (then **€39/export** overage).  
- Mix in MVP: **60% plan / 40% PAYG**.  
- Reviewer prep time (median): **≤ 90 min** (we carry **€5** support per export in model).

### SPONSIO Earnest (sleep template)
- Typical coach pricing: **Base €200** + **Success €300**.  
- Platform take on success component: **8%** *(or €39/mo + 5%; we model 8% case here)*.  
- Kept-rate (after screening): **65%**.  
- Dispute rate: **3%** (handled within support budget).  
- Support minutes per promise (median): **20 min**.

### SPONSIO Virtual (Report Passes)
- 5 passes for **€250** (deferred revenue), **redeemable only for ABDUCTIO exports**.  
- Recognition on redemption; no breakage booked.

---

## B) Per-case unit economics (contribution, not GAAP profit)

### 1) ABDUCTIO export
- **Revenue per export (blend):**  
  `R = 0.40×€59 + 0.60×(€199/6) ≈ 0.40×59 + 0.60×33.17 ≈ €43.7`
- **Variable costs:** infra **€3** + support **€5** = **€8**
- **Contribution per export:**  
  `C_export = R – costs ≈ €43.7 – €8 = **€35.7**`

> Rule of thumb: every **100 exports** add **~€3.6k** contribution.

### 2) Earnest promise (expected value per promise)
- **Our fee when KEPT:** `€300 × 8% = €24`  
  PSP on our fee: `€24 × 2.2% + €0.25 ≈ €0.78` *(platform-side only; merchant PSP on €300 is coach’s cost)*  
  Net fee on KEPT: `€24 – €0.78 = €23.22`
- **Support + infra per promise:** `infra €3 + (20/60h × €30) = €3 + €10 = €13`
- **Contribution if KEPT:** `€23.22 – €13 = **€10.22**`
- **Contribution if NOT KEPT:** platform fee **€0** – infra/support `≈ €13` → **–€13.00**
- **Expected contribution (kept-rate 65%):**  
  `EV = 0.65×€10.22 + 0.35×(–€13.00) ≈ €6.64 – €4.55 = **€2.09 per promise**`

> Read that again: with **€300 success**, **8% take**, **20 min support**, **65% kept-rate**, this lane is **thin** by design (fairness > extractive fees). We make Earnest work at **scale** and by **reducing support minutes** and **raising kept-rate** via better screening/ABDUCTIO.  
> Two easy uplifts: (a) coaches choose **€39/mo + 5%** → higher margin on volume; (b) lower support to **12 min** median → **~€4.09** per promise.

### 3) Virtual voucher
- **Contribution at sale:** **€0** (deferred).  
- **On redemption:** the voucher funds **one ABDUCTIO export** → we book the same **€35.7** contribution per export as above (no separate “voucher margin”).

---

## C) Break-even math (monthly)

Let **F** = monthly fixed costs (dockyard + ops). Illustrative MVP team:
- People: 3 engineers (€6k ea), 1 PM (€6k), 0.5 design (€3k), 1 support (€4k), 0.5 compliance (€3k) → **€34k**  
- Infra baseline & tools: **€6k**  
- **F ≈ €40k / month**

**Break-even via ABDUCTIO alone:**  
`Exports needed = F / C_export = 40,000 / 35.7 ≈ **1,120 exports / mo**`

**Break-even via Earnest alone (thin EV):**  
`Promises needed = F / EV_promise = 40,000 / 2.09 ≈ **19,140 promises / mo**` *(not our plan)*

**Real plan (mix):** ABDUCTIO carries most of the margin; Earnest adds incremental margin and strategic proof.  
Example mix target: **600 exports/mo** (~€21.4k contribution) + **3,000 Earnest promises/mo** (~€6.3k contribution at €2.09) → **€27.7k**; remaining **€12.3k** covered by (i) raising ABDUCTIO volume, (ii) shifting Earnest to **€39/mo + 5%** and/or (iii) cutting support minutes.

---

## D) CAC & payback (coach vs reviewer)

**Reviewer (ABDUCTIO)**
- CAC (partner-led onboarding): **€150** (sales time + collateral).  
- Contribution per month per firm: assume **10 exports/mo** → `10 × €35.7 = **€357**`  
- **Payback ≈ 0.4 mo**; very attractive.

**Coach (Earnest—Sleep)**
- CAC: **€200** (small-cohort outreach + onboarding).  
- Promises per coach per month: **8** (MVP).  
- Contribution per coach per month: `8 × €2.09 ≈ **€16.7**` *(thin in 8%/€300/20min world)*  
- **Payback ≈ 12 mo** → too slow.  
  - With **€39/mo + 5%** plan and support at **12 min**, EV rises to **~€4–6/promise**; at **12–16 promises/coach/mo** payback → **2–3 mo**.  
  - Or increase success component (coach value) to **€400** at same 8% → EV **~€4.7/promise**.

**Conclusion:** we **optimize Earnest** for (a) coaches on **SaaS + 5%**, (b) **more promises per coach**, (c) **lower support minutes**, not for high take-rates.

---

## E) 12-month ramp (illustrative, gated)

| Month | ABDUCTIO exports | Earnest promises | Vouchers redeemed | Revenue (€) | Contribution (€) | Notes |
|---|---:|---:|---:|---:|---:|---|
| 1 | 40 | 60 | 0 | 2,220 | 1,430 | Pilot weeks |
| 2 | 120 | 180 | 0 | 6,660 | 4,290 | Templates tighten |
| 3 | 200 | 300 | 0 | 11,100 | 7,150 | First Case Briefs |
| 4 | 260 | 500 | 50 | 15,340 | 9,600 | Auto-decision ≥90% |
| 5 | 340 | 800 | 120 | 20,910 | 12,900 | Disputes ≤3% |
| 6 | 420 | 1,100 | 200 | 26,480 | 16,200 | Launch Virtual |
| 7 | 520 | 1,500 | 320 | 33,380 | 20,200 | 35% voucher funding |
| 8 | 620 | 1,900 | 430 | 40,280 | 24,300 | 60% voucher funding |
| 9 | 720 | 2,300 | 540 | 47,180 | 28,400 | |
| 10 | 820 | 2,700 | 650 | 54,080 | 32,500 | |
| 11 | 920 | 3,000 | 760 | 60,980 | 36,600 | |
| 12 | 1,020 | 3,200 | 820 | 66,520 | 39,200 | Gate review for next domain |

**How to read it (simplified):**
- **Revenue** = ABDUCTIO export revenue + platform fees on kept success components (we hide VAT for clarity).  
- **Contribution** uses `€35.7/export` and `€2.09/promise` EV; vouchers just time-shift ABDUCTIO.  
- With **F ≈ €40k**, we approach **break-even** around Month 12 under *conservative Earnest*.  
- Two levers to bring break-even forward to Month **9–10**:  
  1) Push exports to **1,200/mo** (reviewer lane scales fast).  
  2) Shift **60–70%** of coaches to **€39/mo + 5%** and cut support minutes to **12–15**.

---

## F) Sensitivity (what actually matters)

| Lever | +10% impact | Why it matters |
|---|---|---|
| **ABDUCTIO exports** | +€3.6k / 100 exports | Biggest contributor; easy to scale with partners |
| **Support minutes (Earnest)** | –€3.33/promise per +10 min | The difference between thin and workable |
| **Kept-rate** | +€1.02/promise per +5pp | Screening + ABDUCTIO clarity drive this |
| **Success component** | +€0.80/promise per +€50 | Coaches can price for value; we keep take modest |
| **Take-rate** | +€3/promise if +1pp | Use carefully; fairness > extraction |
| **Plan mix (ABDUCTIO)** | –€(€59→€33) unit revenue | Plans lower rev/export but increase volume & stickiness |

**Playbook:** never “solve” with higher take-rates; solve with **better templates (higher kept-rate), less support, and more exports.**

---

## G) Financial gates (we won’t scale without these)

- **Contribution margin positive per boat** for **2 consecutive months**.  
- **CAC < ⅓** of 6-month **gross margin** (per lane).  
- **Time-to-cash < 30 days** (no aging tail).  
- **Ops load:** median support **≤ 20 min** (on path to **≤ 12–15 min**).  
- **Legal gates green** (no custody; voucher confusion < 2%).

---

## H) Cash runway & burn (illustrative)

- Fixed burn **€40k/mo**; initial cash **€300k** → **~7.5 months** runway **pre-revenue**.  
- With the ramp above (contribution growing from ~€1.4k → ~€39k/mo), net burn shrinks and crosses **break-even** ~Month **12** (or Month **9–10** with the levers above).  
- We **do not** hire ahead of green gates; boats that miss gates pause and stop consuming growth spend.

---

## I) What an investor (or member) should watch monthly

- **ABDUCTIO:** exports, acceptance %, prep time, contribution.  
- **Earnest:** kept-rate, auto-decision %, disputes %, support minutes, contribution EV/promise.  
- **Virtual:** % exports funded by passes; confusion tickets %.  
- **Unit economics:** CAC, payback (coach vs reviewer), time-to-cash.  
- **Gates dashboard:** tech/legal/market/econ stoplights.

**Bottom line:** this model breaks even by **doing the boring things well**—exports in volume, fair outcome fees with low support, and vouchers that fund analysis without touching money rules. If any gate turns red, the spend stops until the math—and the law—are green again.
