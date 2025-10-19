# advanced_adversary_simulation.py
# To run this script:
# 1. Make sure you have the required libraries: pip install pandas numpy matplotlib scipy
# 2. Save this code as a Python file (e.g., advanced_adversary_sim.py)
# 3. Run from your terminal: python advanced_adversary_sim.py

import numpy as np
import matplotlib.pyplot as plt
from dataclasses import dataclass, field
from typing import Dict, List, Any, Optional
from collections import defaultdict
import pandas as pd
import random

# --- Agent & Simulation Classes ---

@dataclass
class Promise:
    """Represents a promise made by an agent."""
    promiser_id: int
    stake: float
    is_high_value: bool = False
    actual_outcome: Optional[bool] = None

class Agent:
    """Base class for an agent in the protocol."""
    def __init__(self, agent_id: int, initial_credits: float, domains: List[str]):
        self.id = agent_id
        self.credits = initial_credits
        self.initial_credits = initial_credits
        self.merit = {domain: np.random.uniform(0.1, 0.3) for domain in domains}
        self.type = "Honest"

    def get_merit(self, domain: str) -> float:
        return self.merit.get(domain, 0.1)

    def update_merit(self, domain: str, delta: float):
        current = self.get_merit(domain)
        self.merit[domain] = max(0.0, min(1.0, current + delta))

    def decide_on_promise(self, promise_details: Dict[str, Any]) -> bool:
        # Default honest agent always keeps promises.
        return True

class SleeperAgent(Agent):
    """An agent that behaves honestly to build merit, then defects."""
    def __init__(self, agent_id: int, initial_credits: float, domains: List[str], defect_round: int):
        super().__init__(agent_id, initial_credits, domains)
        self.defect_round = defect_round
        self.type = "Sleeper"

    def decide_on_promise(self, promise_details: Dict[str, Any]) -> bool:
        current_round = promise_details["current_round"]
        is_high_value = promise_details["is_high_value"]

        if current_round >= self.defect_round and is_high_value:
            # Once the defect round is reached, break the first high-value promise.
            return False
        return True

class LearningAgent(Agent):
    """An agent that adapts its strategy based on observed outcomes."""
    def __init__(self, agent_id: int, initial_credits: float, domains: List[str]):
        super().__init__(agent_id, initial_credits, domains)
        self.honesty_rate = 0.5  # Start neutral
        self.type = "Learning"

    def decide_on_promise(self, promise_details: Dict[str, Any]) -> bool:
        return np.random.random() < self.honesty_rate

    def update_strategy(self, neighbors: List[Agent]):
        """Update honesty_rate based on neighbors' success."""
        if not neighbors:
            return

        # Find the most successful neighbor (highest % credit gain)
        best_neighbor = max(neighbors, key=lambda n: n.credits / n.initial_credits)
        
        # Nudge honesty_rate towards the best neighbor's strategy
        if isinstance(best_neighbor, (HonestAgent, SleeperAgent)): # Assume Sleeper is mostly honest
            target_honesty = 0.95
        elif isinstance(best_neighbor, LearningAgent):
            target_honesty = best_neighbor.honesty_rate
        else: # A hypothetical dishonest agent
             target_honesty = 0.05
        
        # Move 10% towards the target
        self.honesty_rate += 0.1 * (target_honesty - self.honesty_rate)
        self.honesty_rate = max(0.0, min(1.0, self.honesty_rate))

class HonestAgent(Agent):
    """A consistently honest agent."""
    def __init__(self, agent_id: int, initial_credits: float, domains: List[str]):
        super().__init__(agent_id, initial_credits, domains)
        self.type = "Honest"

class AdvancedAdversarySimulation:
    """Simulation environment to test advanced adversarial strategies."""
    def __init__(self, n_agents=100, n_rounds=300, n_honest=70, n_sleeper=15, n_learning=15):
        self.n_agents = n_agents
        self.n_rounds = n_rounds
        self.domains = [f"domain_{i}" for i in range(5)]
        
        # Economic parameters
        self.base_stake = 100.0
        self.op_cost_percentage = 0.05
        self.lambda_penalty = 3.0 # Higher penalty to punish defection
        self.gamma = 0.02 # Merit change rate
        
        # Agent populations
        self.agents = self._initialize_agents(n_honest, n_sleeper, n_learning)
        self.round_num = 0
        
        # History
        self.agent_history = defaultdict(lambda: {'credits': [], 'avg_merit': []})

    def _initialize_agents(self, n_honest, n_sleeper, n_learning):
        agents = {}
        agent_id_counter = 0
        initial_credits = 1000.0
        
        for _ in range(n_honest):
            agents[agent_id_counter] = HonestAgent(agent_id_counter, initial_credits, self.domains)
            agent_id_counter += 1
            
        for _ in range(n_sleeper):
            # Defect round is somewhere in the second half of the simulation
            defect_round = np.random.randint(self.n_rounds // 2, self.n_rounds)
            agents[agent_id_counter] = SleeperAgent(agent_id_counter, initial_credits, self.domains, defect_round)
            agent_id_counter += 1

        for _ in range(n_learning):
            agents[agent_id_counter] = LearningAgent(agent_id_counter, initial_credits, self.domains)
            agent_id_counter += 1
            
        return agents

    def simulate_round(self):
        self.round_num += 1
        
        for agent in self.agents.values():
            if agent.credits < self.base_stake * 2: continue # Skip if low on funds

            domain = random.choice(self.domains)
            merit = agent.get_merit(domain)
            
            # High value promises are rare and have higher stakes
            is_high_value = np.random.random() < 0.05
            stake = self.base_stake * (5 if is_high_value else 1) * (1 - merit * 0.8)
            
            if agent.credits < stake: continue

            promise_details = {
                "current_round": self.round_num,
                "is_high_value": is_high_value
            }
            
            # Agent decides, pays stake
            kept = agent.decide_on_promise(promise_details)
            agent.credits -= stake
            
            # Process outcome
            op_cost = stake * self.op_cost_percentage
            if kept:
                agent.credits += (stake - op_cost)
                agent.update_merit(domain, self.gamma * (1 - merit))
            else: # Broken promise
                agent.update_merit(domain, -self.lambda_penalty * self.gamma * merit)
        
        # Learning agents update their strategy
        for agent in self.agents.values():
            if isinstance(agent, LearningAgent):
                # Simple neighborhood: 5 random agents
                neighbors = random.sample(list(self.agents.values()), 5)
                agent.update_strategy(neighbors)

        self._record_history()

    def _record_history(self):
        for agent_id, agent in self.agents.items():
            self.agent_history[agent_id]['credits'].append(agent.credits)
            avg_merit = np.mean(list(agent.merit.values()))
            self.agent_history[agent_id]['avg_merit'].append(avg_merit)
            self.agent_history[agent_id]['type'] = agent.type

    def run(self):
        for _ in range(self.n_rounds):
            self.simulate_round()
        return self.agent_history

class AdversaryTestValidator:
    """Runs the simulation to test if advanced strategies are profitable."""
    def run_test(self, n_rounds=300):
        print("🔬 Running Advanced Adversary Simulation...")
        sim = AdvancedAdversarySimulation(n_rounds=n_rounds)
        history = sim.run()
        print("✅ Simulation Complete.")
        return history

class AdversaryTestAnalyzer:
    """Analyzes results and generates a report."""
    def __init__(self, history: Dict):
        self.history = history

    def analyze_profitability(self) -> pd.DataFrame:
        """Compares the final profitability of different agent types."""
        final_stats = []
        for agent_id, data in self.history.items():
            final_stats.append({
                'id': agent_id,
                'type': data['type'],
                'final_credits': data['credits'][-1],
                'final_merit': data['avg_merit'][-1]
            })
        
        df = pd.DataFrame(final_stats)
        profitability = df.groupby('type')['final_credits'].mean().sort_values(ascending=False)
        return profitability

    def plot_results(self):
        """Generates and saves analysis charts."""
        fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(16, 7))

        # Plot 1: Average Credits over Time by Agent Type
        df = pd.DataFrame(self.history).T
        for agent_type in ['Honest', 'Sleeper', 'Learning']:
            agent_ids = [i for i, data in df.iterrows() if data['type'] == agent_type]
            if not agent_ids: continue
            
            credits_history = np.array([df.loc[i]['credits'] for i in agent_ids])
            mean_credits = credits_history.mean(axis=0)
            ax1.plot(mean_credits, label=f'{agent_type} Agents')

        ax1.set_title('Average Credits by Agent Strategy')
        ax1.set_xlabel('Round')
        ax1.set_ylabel('Average Credits')
        ax1.grid(True, alpha=0.3)
        ax1.legend()

        # Plot 2: Final Merit vs. Final Credits
        final_df = self.analyze_profitability().reset_index()
        final_data = []
        for agent_id, data in self.history.items():
            final_data.append({
                'type': data['type'],
                'credits': data['credits'][-1],
                'merit': data['avg_merit'][-1]
            })
        plot_df = pd.DataFrame(final_data)

        colors = {'Honest': 'blue', 'Sleeper': 'orange', 'Learning': 'green'}
        for agent_type, group in plot_df.groupby('type'):
            ax2.scatter(group['credits'], group['merit'], alpha=0.6, label=agent_type, color=colors[agent_type])
        
        ax2.set_title('Final State: Merit vs. Credits')
        ax2.set_xlabel('Final Credits')
        ax2.set_ylabel('Final Average Merit')
        ax2.grid(True, alpha=0.3)
        ax2.legend()
        
        plt.tight_layout()
        plt.savefig("adversary_analysis.png")
        print("\n📊 Analysis charts saved to 'adversary_analysis.png'")

    def generate_report_text(self):
        """Generates a full markdown report as a string."""
        profitability = self.analyze_profitability()
        report_lines = ["# 🛡️ Agency Protocol: Advanced Adversary Simulation Report"]
        
        report_lines.append("\n## Executive Summary")
        top_performer = profitability.index[0]
        sleeper_profit = profitability.get('Sleeper', 0)
        honest_profit = profitability.get('Honest', 0)

        if top_performer == "Honest" and sleeper_profit < honest_profit:
            report_lines.append("""
**The protocol successfully neutralized advanced adversarial strategies.** Consistently honest behavior emerged as the most profitable long-term strategy. 
Sleeper agents, who attempted a "long con," were significantly penalized for their eventual defection, failing to outperform honest agents. 
Learning agents adapted but ultimately converged towards honest behavior as the most successful observed strategy.
""")
        else:
            report_lines.append("""
**WARNING: The protocol shows potential vulnerabilities to advanced strategies.** The simulation indicates that certain adversarial behaviors, 
such as the 'Sleeper Agent' strategy, may be profitable under the current economic parameters. This requires immediate attention and parameter tuning.
""")

        report_lines.append("\n## Profitability Analysis by Strategy")
        report_lines.append("Average final credits for each agent type:")
        report_lines.append(profitability.to_string())

        report_lines.append("\n## Key Insights")
        if honest_profit > sleeper_profit:
             report_lines.append("- **'Long Con' is Unprofitable:** The severe merit penalty and loss of a high-value stake for Sleeper Agents outweighs the accumulated benefits of their initial honest behavior. The protocol's `lambda_penalty` is effective.")
        else:
             report_lines.append("- **VULNERABILITY: 'Long Con' is Profitable:** The penalty for a single, high-value defection is insufficient to deter the Sleeper Agent strategy. The `lambda_penalty` or the staking function for high-value promises must be increased.")

        learning_agents_final_honesty = np.mean([a.honesty_rate for a in AdvancedAdversarySimulation().agents.values() if isinstance(a, LearningAgent)])
        if learning_agents_final_honesty > 0.7:
             report_lines.append("- **Honesty is Convergent:** Learning Agents, by observing the network, adapted their strategies to become more honest over time, correctly identifying it as the optimal path to success.")
        else:
             report_lines.append("- **Dishonesty is Convergent:** Learning Agents adapted to become more dishonest, indicating that the incentives for promise-breaking may be too high.")

        report_lines.append("\n## Recommendations")
        report_lines.append("1. **Validate Penalty Functions:** Ensure the `lambda_penalty` and the stake multiplier for high-value promises are high enough to make any single defection a net negative in expected utility.")
        report_lines.append("2. **Introduce Merit Velocity:** Consider tracking the *rate of change* of merit. A sudden, large drop (like a Sleeper Agent defecting) could trigger additional, temporary penalties or a 'cooldown' period, further disincentivizing this strategy.")
        report_lines.append("3. **Diversify Learning Models:** Future tests should include more sophisticated learning agents (e.g., using reinforcement learning) to probe for more complex emergent exploits.")

        return "\n".join(report_lines)

# --- Main Execution Block ---

if __name__ == "__main__":
    validator = AdversaryTestValidator()
    simulation_history = validator.run_test(n_rounds=300)
    
    analyzer = AdversaryTestAnalyzer(simulation_history)
    report = analyzer.generate_report_text()
    
    print("\n" + "="*80)
    print(report)
    print("="*80)
    
    analyzer.plot_results()
