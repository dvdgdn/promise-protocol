# treasury_stress_test_core.py
# To run this script:
# 1. Make sure you have the required libraries: pip install pandas numpy matplotlib scipy
# 2. Save this code as a Python file (e.g., treasury_test_core.py)
# 3. Run from your terminal: python treasury_test_core.py

import numpy as np
import matplotlib.pyplot as plt
from dataclasses import dataclass, field
from typing import Dict, List, Tuple, Optional
from collections import defaultdict
import pandas as pd
from scipy import stats

# --- Simulation Code ---

@dataclass
class Promise:
    """Represents a promise made by an agent"""
    promiser_id: int
    domain: str
    stake: float
    actual_outcome: Optional[bool] = None

@dataclass
class Agent:
    """Represents an agent in the protocol"""
    id: int
    credits: float
    merit: Dict[str, float] = field(default_factory=dict)
    honesty_rate: float = 0.95

class TreasuryStressTestSimulation:
    """
    An enhanced simulation that includes a protocol treasury to test
    long-term economic sustainability.
    """
    def __init__(self,
                 n_agents: int = 100,
                 n_rounds: int = 200,
                 base_stake: float = 100.0,
                 op_cost_percentage: float = 0.05, # The % of stake that is the operational cost
                 computation_cost_per_round: float = 250.0, # Infrastructure cost
                 initial_credits: float = 1000.0,
                 initial_treasury: float = 10000.0):

        # Core parameters
        self.n_agents = n_agents
        self.n_rounds = n_rounds
        self.domains = [f"domain_{i}" for i in range(5)]
        
        # Economic model parameters
        self.base_stake = base_stake
        self.op_cost_percentage = op_cost_percentage
        self.computation_cost_per_round = computation_cost_per_round
        self.initial_credits = initial_credits
        
        # State variables
        self.agents = self._initialize_agents()
        self.treasury_balance = initial_treasury
        
        # History tracking
        self.treasury_history = []
        self.promise_volume_history = []
        self.round_num = 0

    def _initialize_agents(self) -> Dict[int, Agent]:
        agents = {}
        for i in range(self.n_agents):
            honesty_rate = np.random.choice([0.95, 0.6], p=[0.9, 0.1])
            agent = Agent(id=i, credits=self.initial_credits, honesty_rate=honesty_rate)
            for domain in self.domains:
                agent.merit[domain] = np.random.uniform(0.1, 0.3)
            agents[i] = agent
        return agents

    def calculate_stake_requirement(self, agent: Agent, domain: str) -> float:
        merit = agent.merit.get(domain, 0.1)
        discount = merit * 0.8
        return self.base_stake * (1 - discount)

    def simulate_round(self):
        self.round_num += 1
        promises_this_round = 0

        # 1. Agents make promises
        for agent in self.agents.values():
            if agent.credits < self.base_stake: continue
            
            domain = random.choice(self.domains)
            stake = self.calculate_stake_requirement(agent, domain)
            if agent.credits < stake: continue

            # Agent makes promise, pays stake
            agent.credits -= stake
            promises_this_round += 1
            
            # Treasury collects the operational cost component
            op_cost = stake * self.op_cost_percentage
            self.treasury_balance += op_cost
            
            # Process outcome (simplified for this test)
            if np.random.random() < agent.honesty_rate: # Promise Kept
                agent.credits += (stake - op_cost) # Get at-risk portion back
                agent.merit[domain] = min(1.0, agent.merit[domain] + 0.01 * (1 - agent.merit[domain]))
            else: # Promise Broken
                agent.merit[domain] = max(0.0, agent.merit[domain] - 0.05 * agent.merit[domain])

        # 2. Treasury pays for infrastructure
        self.treasury_balance -= self.computation_cost_per_round
        
        # 3. Record history
        self.treasury_history.append(self.treasury_balance)
        self.promise_volume_history.append(promises_this_round)

    def run(self):
        """Runs the simulation for the configured number of rounds."""
        for i in range(self.n_rounds):
            self.simulate_round()
            if self.treasury_balance <= 0:
                print(f"  - Treasury bankrupt at round {i+1}. Halting simulation.")
                break
        return self.treasury_history, self.promise_volume_history

# --- Validation Suite ---

class TreasuryTestValidator:
    """
    Runs the TreasuryStressTestSimulation across a range of parameters
    to validate economic sustainability.
    """
    def __init__(self, n_agents=100, n_rounds=300):
        self.n_agents = n_agents
        self.n_rounds = n_rounds
        self.results = []

    def test_economic_sustainability(self, op_cost_range: List[float]):
        """
        Runs the simulation for each operational cost percentage in the range.
        """
        print("🔬 Running Validation Suite...")
        
        for i, op_cost_pct in enumerate(op_cost_range):
            print(f"  Testing Op Cost = {op_cost_pct:.1%}...")
            # Estimate computation cost based on number of agents
            computation_cost = 50 + (self.n_agents * 2)

            sim = TreasuryStressTestSimulation(
                n_agents=self.n_agents,
                n_rounds=self.n_rounds,
                op_cost_percentage=op_cost_pct,
                computation_cost_per_round=computation_cost
            )
            treasury_history, _ = sim.run()
            
            # Analyze the stability of the treasury
            is_solvent = treasury_history[-1] > 0 if treasury_history else False
            
            # Use linear regression on log-transformed data to check for explosive growth
            log_history = np.log([max(1, h) for h in treasury_history])
            if len(log_history) > 10:
                slope, _, _, _, _ = stats.linregress(range(len(log_history)), log_history)
            else:
                slope = 0

            self.results.append({
                "op_cost_pct": op_cost_pct,
                "is_solvent": is_solvent,
                "final_balance": treasury_history[-1] if treasury_history else 0,
                "stability_slope": slope,
                "history": treasury_history
            })
        
        print("✅ Validation Suite Complete.")
        return self.results

# --- Analysis and Reporting ---

class TreasuryTestAnalyzer:
    """
    Analyzes the validation results and generates a comprehensive report.
    """
    def __init__(self, validation_results: List[Dict]):
        self.results_df = pd.DataFrame(validation_results)

    def find_sweet_spot(self) -> Optional[Dict]:
        """Identifies the optimal op_cost_percentage."""
        sustainable_results = self.results_df[self.results_df['is_solvent'] == True]
        if sustainable_results.empty:
            return None
        
        # The "sweet spot" is the lowest op_cost that is solvent and has a low stability slope
        sustainable_results = sustainable_results[sustainable_results['stability_slope'] < 0.01]
        if sustainable_results.empty:
            return None
            
        return sustainable_results.sort_values(by="op_cost_pct").iloc[0].to_dict()

    def generate_report_text(self):
        """Generates a full markdown report as a string."""
        sweet_spot = self.find_sweet_spot()
        report_lines = []

        report_lines.append("# 📈 Agency Protocol: Treasury Stress Test Report")
        report_lines.append("\n## Executive Summary")
        
        if sweet_spot:
            report_lines.append(f"""
**The protocol demonstrates strong economic sustainability.** A stable equilibrium was found, 
preventing both bankruptcy and explosive value extraction.

The optimal **Operational Cost (`c_op`) is around {sweet_spot['op_cost_pct']:.1%}**. At this level, 
the protocol's treasury remains solvent while its growth is stable, ensuring long-term viability.
""")
        else:
            report_lines.append("""
**The protocol's economic model is unstable under the tested parameters.** No "sweet spot" was found
where the treasury could reliably cover its costs without either going bankrupt or growing explosively.
This indicates a critical need for parameter tuning before deployment.
""")

        report_lines.append("\n## Key Insights")
        insolvency_threshold = self.results_df[self.results_df['is_solvent'] == False]['op_cost_pct'].max()
        if pd.notna(insolvency_threshold):
            report_lines.append(f"- **Insolvency Threshold:** The protocol is not viable with an operational cost below **{insolvency_threshold:.1%}**.")
        
        if sweet_spot:
            report_lines.append(f"- **Optimal Stability Zone:** The most stable, non-explosive growth occurs at an operational cost of **~{sweet_spot['op_cost_pct']:.1%}**.")
        
        explosive_threshold = self.results_df[self.results_df['stability_slope'] > 0.01]['op_cost_pct'].min()
        if pd.notna(explosive_threshold):
            report_lines.append(f"- **Value Extraction Risk:** Costs above **{explosive_threshold:.1%}** lead to exponential treasury growth, which could drain too much value from the ecosystem.")

        report_lines.append("\n## Recommendations")
        report_lines.append("1. **Set Initial `c_op` Conservatively:** Launch the protocol with an operational cost within the identified stable zone (e.g., **{:.1%}**).".format(sweet_spot['op_cost_pct']) if sweet_spot else "N/A")
        report_lines.append("2. **Implement Dynamic Cost Adjustment:** The `computation_cost_per_round` will fluctuate. The protocol should implement a governance mechanism (`GovernanceAgent`) to dynamically adjust the `op_cost_percentage` in response to real-world infrastructure costs.")
        report_lines.append("3. **Establish a Treasury Buffer:** The protocol should aim to maintain a treasury balance that can cover several months of operational expenses to withstand periods of low activity.")

        report_lines.append("\n## Detailed Validation Data")
        report_lines.append(self.results_df.to_string(formatters={
            "op_cost_pct": "{:.1%}".format,
            "final_balance": "{:,.0f}".format,
            "stability_slope": "{:.4f}".format
        }))
        
        return "\n".join(report_lines)

    def plot_results(self):
        """Generates and saves the analysis charts."""
        fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 6))

        # Chart 1: Final Treasury Balance vs. Op Cost
        ax1.plot(self.results_df['op_cost_pct'] * 100, self.results_df['final_balance'], 'o-', color="#1f77b4")
        ax1.axhline(0, color='red', linestyle='--', label='Insolvency Line')
        ax1.set_title('Final Treasury Balance vs. Operational Cost', fontsize=14)
        ax1.set_xlabel('Operational Cost Percentage (%)')
        ax1.set_ylabel('Final Treasury Balance')
        ax1.set_yscale('log')
        ax1.grid(True, alpha=0.2)
        ax1.legend()

        # Chart 2: Stability Slope vs. Op Cost
        ax2.plot(self.results_df['op_cost_pct'] * 100, self.results_df['stability_slope'], 'o-', color="#ff7f0e")
        ax2.axhline(0.01, color='green', linestyle='--', label='Stability Zone Upper Bound')
        ax2.axhline(0, color='red', linestyle='--', label='Sustainability Line')
        ax2.set_title('Treasury Growth Stability vs. Operational Cost', fontsize=14)
        ax2.set_xlabel('Operational Cost Percentage (%)')
        ax2.set_ylabel('Log-Growth Slope (Stability)')
        ax2.grid(True, alpha=0.2)
        ax2.legend()
        
        plt.tight_layout()
        plt.savefig("treasury_analysis.png")
        print("\n📊 Analysis charts saved to 'treasury_analysis.png'")

# --- Main Execution Block ---

if __name__ == "__main__":
    # Define test parameters
    N_AGENTS = 100
    N_ROUNDS = 300
    OP_COST_RANGE = np.linspace(0.01, 0.10, 20) # Test op_cost from 1% to 10%

    # Run the validation suite
    validator = TreasuryTestValidator(n_agents=N_AGENTS, n_rounds=N_ROUNDS)
    results_data = validator.test_economic_sustainability(OP_COST_RANGE)
    
    # Analyze the results and generate the report
    analyzer = TreasuryTestAnalyzer(results_data)
    report = analyzer.generate_report_text()
    
    print("\n" + "="*80)
    print(report)
    print("="*80)

    # Generate and save plots
    analyzer.plot_results()

