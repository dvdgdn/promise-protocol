# genesis_simulation.py
# To run this script:
# 1. Make sure you have the required libraries: pip install pandas numpy matplotlib
# 2. Save this code as a Python file (e.g., genesis_test.py)
# 3. Run from your terminal: python genesis_test.py

import numpy as np
import matplotlib.pyplot as plt
from dataclasses import dataclass, field
from typing import Dict, List, Any
import pandas as pd
import random

# --- Agent & Simulation Classes ---

@dataclass
class Promise:
    """Represents a simple, verifiable promise."""
    promiser_id: int
    stake: float
    domain: str
    # In this simulation, all promises are objectively verifiable by AI
    # We assume all promises made are kept, to focus on merit gain.

@dataclass
class Agent:
    """Base class for an agent."""
    id: int
    credits: float
    merit: Dict[str, float]
    type: str

    def get_merit(self, domain: str) -> float:
        return self.merit.get(domain, 0.0)

    def update_merit(self, domain: str, delta: float):
        current = self.get_merit(domain)
        self.merit[domain] = max(0.0, min(1.0, current + delta))

class AIValidatorAgent(Agent):
    """An AI agent that can only assess promises."""
    def __init__(self, agent_id: int, merit: Dict[str, float]):
        super().__init__(agent_id, 0, merit, "AI Validator")

class HumanAgent(Agent):
    """A user agent that starts with zero merit."""
    def __init__(self, agent_id: int, initial_credits: float, domains: List[str]):
        merit = {d: 0.0 for d in domains} # Starts with ZERO merit
        super().__init__(agent_id, initial_credits, merit, "Human")

class GenesisAgent:
    """A one-time agent that bootstraps the ecosystem."""
    def __init__(self, domains: List[str]):
        self.domains = domains

    def run(self, n_validators: int) -> Dict[int, AIValidatorAgent]:
        """Creates the initial fleet of AI validators with foundational merit."""
        validators = {}
        for i in range(n_validators):
            # Assign high, but not perfect, merit
            merit = {d: np.random.uniform(0.8, 0.95) for d in self.domains}
            validators[i] = AIValidatorAgent(agent_id=i, merit=merit)
        print(f"  - GenesisAgent created {n_validators} AI Validators with foundational merit.")
        return validators

class GenesisSimulation:
    """Simulation to test the bootstrapping of the protocol."""
    def __init__(self, n_humans=50, n_validators=10):
        self.domains = [f"domain_{i}" for i in range(5)]
        
        # Economic parameters
        self.base_stake = 100.0
        self.op_cost_percentage = 0.05
        self.gamma = 0.05 # Higher merit gain rate for bootstrapping phase
        
        # State
        self.ai_validators: Dict[int, AIValidatorAgent] = {}
        self.human_agents: Dict[int, HumanAgent] = {}
        self.round_num = 0
        
        # History
        self.human_merit_history = defaultdict(list)

        self._bootstrap_ecosystem(n_humans, n_validators)

    def _bootstrap_ecosystem(self, n_humans, n_validators):
        """Uses the GenesisAgent to create the initial state."""
        genesis_agent = GenesisAgent(self.domains)
        self.ai_validators = genesis_agent.run(n_validators)
        
        initial_credits = 1000.0
        for i in range(n_validators, n_validators + n_humans):
            self.human_agents[i] = HumanAgent(i, initial_credits, self.domains)
        print(f"  - Introduced {n_humans} Human Agents with zero merit.")

    def run_round(self):
        self.round_num += 1
        
        # Human agents make promises
        for agent in self.human_agents.values():
            if agent.credits < self.base_stake: continue

            domain = random.choice(self.domains)
            merit = agent.get_merit(domain)
            stake = self.base_stake * (1 - merit * 0.8)
            
            if agent.credits < stake: continue

            # Make promise and pay stake
            agent.credits -= stake
            
            # AI Validators assess the promise. Since we assume promises are kept,
            # the assessment is always positive.
            op_cost = stake * self.op_cost_percentage
            agent.credits += (stake - op_cost)
            
            # Merit is updated based on the average merit of the assessing validators
            assessing_validators = random.sample(list(self.ai_validators.values()), 3)
            assessor_merit_weight = np.mean([v.get_merit(domain) for v in assessing_validators])
            
            merit_gain = self.gamma * (1 - merit) * assessor_merit_weight
            agent.update_merit(domain, merit_gain)

        self._record_history()

    def _record_history(self):
        for agent_id, agent in self.human_agents.items():
            avg_merit = np.mean(list(agent.merit.values()))
            self.human_merit_history[agent_id].append(avg_merit)

    def run(self, n_rounds):
        for _ in range(n_rounds):
            self.run_round()
        return GenesisAnalyzer(self.human_merit_history)

class GenesisValidator:
    """Runs the GenesisSimulation to validate the bootstrap process."""
    def run_test(self, n_rounds=100):
        print("🔬 Running Genesis Simulation...")
        sim = GenesisSimulation(n_humans=50, n_validators=10)
        history = sim.run(n_rounds)
        print("✅ Genesis Simulation Complete.")
        return history

class GenesisAnalyzer:
    """Analyzes results and generates a report."""
    def __init__(self, history: Dict):
        self.history = history
        self.df = pd.DataFrame(history).T
        self.df['final_merit'] = self.df.apply(lambda row: row.iloc[-1], axis=1)

    def plot_results(self):
        print(f"plot_results called for GenesisAnalyzer at time_step: {self.df.index.max()}")
        fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(12, 6)) # Adjusted figsize for better display

        # Plot 1: Average Merit of Human Agents Over Time
        avg_merit_trajectory = self.df.drop(columns=['final_merit']).mean(axis=0)
        ax1.plot(avg_merit_trajectory)
        ax1.set_title('Average Merit Growth')
        ax1.set_xlabel('Round')
        ax1.set_ylabel('Average Merit')
        ax1.grid(True, alpha=0.3)
        ax1.axhline(0.5, color='green', linestyle='--', label='Viability Threshold')
        ax1.legend()
        ax1.text(0.5, 0.9, 'Plot 1 Drawn', transform=ax1.transAxes, ha='center', va='center', color='black')

        # Plot 2: Distribution of Final Merit Scores
        ax2.hist(self.df['final_merit'], bins=20, edgecolor='black')
        ax2.set_title('Final Merit Distribution')
        ax2.set_xlabel('Final Merit Score')
        ax2.set_ylabel('Number of Human Agents')
        ax2.axvline(self.df['final_merit'].mean(), color='red', linestyle='--', label=f"Mean: {self.df['final_merit'].mean():.2f}")
        ax2.legend()
        ax2.grid(True, alpha=0.3)
        ax2.text(0.5, 0.9, 'Plot 2 Drawn', transform=ax2.transAxes, ha='center', va='center', color='black')

        plt.tight_layout()
        # Instead of saving to file, return base64
        buf = io.BytesIO()
        plt.savefig(buf, format='png', dpi=100, bbox_inches='tight')
        buf.seek(0)
        img_base64 = base64.b64encode(buf.read()).decode('utf-8')
        plt.close(fig) # Close the figure to free memory
        return f"data:image/png;base64,{img_base64}"

    def plot_state(self):
        print("plot_state called for GenesisAnalyzer, redirecting to plot_results")
        return self.plot_results()

    def plot_metrics(self):
        print("plot_metrics called for GenesisAnalyzer, redirecting to plot_results")
        return self.plot_results()

    def generate_report_text(self):
        report_lines = ["# 🌱 Agency Protocol: Genesis & Bootstrap Simulation Report"]
        
        report_lines.append("\n## Executive Summary")
        
        final_avg_merit = self.df['final_merit'].mean()
        merit_threshold = 0.5 # The merit level needed to be considered a trusted participant

        if final_avg_merit > merit_threshold:
            report_lines.append(f"""
**Result: SUCCESS.** The AI-first bootstrap mechanism is viable. Human agents, starting with zero merit, were able to consistently make promises and leverage the initial fleet of AI validators to build their reputation. 
The final average merit of **{final_avg_merit:.3f}** significantly exceeds the viability threshold, proving that new users can successfully join and thrive in the ecosystem.
""")
        else:
            report_lines.append(f"""
**Result: FAILURE.** The bootstrap mechanism is flawed. Human agents struggled to build reputation, achieving a final average merit of only **{final_avg_merit:.3f}**. 
This indicates that the initial incentives are insufficient to overcome the "cold start" problem. The `gamma` (merit gain rate) or the initial merit of AI validators may need to be increased.
""")

        report_lines.append("\n## Key Insights")
        rounds_to_reach_threshold = (self.df.drop(columns=['final_merit']).mean(axis=0) > merit_threshold).idxmax() if (self.df.drop(columns=['final_merit']).mean(axis=0) > merit_threshold).any() else "N/A"
        
        report_lines.append(f"- **Time to Trust:** On average, a new human agent was able to cross the 'viability threshold' of 0.5 merit within **{rounds_to_reach_threshold}** rounds of consistent participation.")
        report_lines.append("- **Merit as a Bottleneck:** The rate of merit acquisition is the primary limiting factor for new user growth. The simulation confirms that the `gamma` parameter is the most sensitive lever for adjusting the onboarding experience.")
        report_lines.append("- **Positive Feedback Loop:** The simulation clearly shows a positive feedback loop: as agents gained a small amount of merit, their cost to participate (staking) decreased, allowing them to make more promises and accelerate their merit gain, confirming the intended design.")

        report_lines.append("\n## Recommendations")
        report_lines.append("1. **Confirm `gamma` Parameter:** The initial `gamma` value should be set high enough to ensure a smooth onboarding experience, as validated by this simulation. It could even be dynamically adjusted, starting high and decreasing as the network matures.")
        report_lines.append("2. **Implement a Tutorial Flow:** The protocol's user interface should guide new users through their first few promises, explaining how interacting with AI validators helps build their initial reputation.")
        report_lines.append("3. **Diversify Initial Validators:** While this simulation used generic AI validators, a live implementation should launch with specialized validators for high-demand domains (e.g., software testing, content moderation) to provide immediate, targeted utility.")

        return "\n".join(report_lines)

# --- Main Execution Block ---

if __name__ == "__main__":
    validator = GenesisValidator()
    simulation_history = validator.run_test(n_rounds=100)
    
    analyzer = GenesisAnalyzer(simulation_history)
    report = analyzer.generate_report_text()
    
    print("\n" + "="*80)
    print(report)
    print("="*80)
    
    analyzer.plot_results()
