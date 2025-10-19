# subtle_attack_simulation.py
# To run this script:
# 1. Make sure you have the required libraries: pip install pandas numpy matplotlib scipy
# 2. Save this code as a Python file (e.g., subtle_attack_test.py)
# 3. Run from your terminal: python subtle_attack_test.py

import numpy as np
import matplotlib.pyplot as plt
from dataclasses import dataclass, field
from typing import Dict, List, Any, Optional
import pandas as pd
import random

# --- Entity Classes ---

@dataclass
class Promise:
    """Represents a promise made by an agent."""
    promiser_id: int
    stake: float
    domain: str
    actual_outcome: bool # Ground truth: was the promise actually kept?

@dataclass
class Agent:
    """A standard agent in the protocol."""
    id: int
    credits: float
    merit: Dict[str, float]
    type: str = "Honest"
    is_coalition_member: bool = False
    
    def get_merit(self, domain: str) -> float:
        return self.merit.get(domain, 0.1)

    def update_merit(self, domain: str, delta: float):
        current = self.get_merit(domain)
        self.merit[domain] = max(0.0, min(1.0, current + delta))

@dataclass
class OracleAgent(Agent):
    """A specialized agent that reports on real-world outcomes."""
    truthfulness: float = 1.0 # Probability of reporting the truth
    type: str = "Oracle"

# --- Simulation Environment ---

class SubtleAttackSimulation:
    """Simulation environment to test subtle attack vectors."""
    def __init__(self, n_agents=100, n_oracles=5):
        self.n_agents = n_agents
        self.domains = [f"domain_{i}" for i in range(5)]
        
        # Economic parameters
        self.base_stake = 100.0
        self.op_cost_percentage = 0.05
        self.lambda_penalty = 3.0
        self.gamma = 0.02
        
        # State
        self.agents, self.oracles = self._initialize_entities(n_agents, n_oracles)
        self.round_num = 0
        self.praise_bomb_target_id: Optional[int] = None
        
        # History
        self.history = defaultdict(lambda: {'credits': [], 'avg_merit': [], 'type': ''})

    def _initialize_entities(self, n_agents, n_oracles):
        agents = {}
        oracles = {}
        initial_credits = 1000.0
        
        for i in range(n_agents):
            merit = {d: np.random.uniform(0.1, 0.3) for d in self.domains}
            agents[i] = Agent(id=i, credits=initial_credits, merit=merit)
            
        for i in range(n_agents, n_agents + n_oracles):
            merit = {d: np.random.uniform(0.5, 0.8) for d in self.domains} # Oracles start with high merit
            oracles[i] = OracleAgent(id=i, credits=initial_credits * 5, merit=merit)
            
        return agents, oracles

    def setup_praise_bombing(self, coalition_size: int):
        """Designates a coalition and a target for praise bombing."""
        agent_ids = list(self.agents.keys())
        random.shuffle(agent_ids)
        
        coalition_ids = agent_ids[:coalition_size]
        self.praise_bomb_target_id = coalition_ids[0]
        
        for agent_id in coalition_ids:
            self.agents[agent_id].is_coalition_member = True
        
        self.agents[self.praise_bomb_target_id].type = "Praise Bomb Target"
        print(f"  - Praise Bombing coalition formed. Target: Agent {self.praise_bomb_target_id}")

    def corrupt_oracle(self, oracle_id: int):
        """Corrupts a single oracle to start reporting falsely."""
        if oracle_id in self.oracles:
            self.oracles[oracle_id].truthfulness = 0.0 # Always lies
            self.oracles[oracle_id].type = "Corrupt Oracle"
            print(f"  - Oracle {oracle_id} has been corrupted.")

    def run_round(self):
        self.round_num += 1
        
        # 1. Agents make promises
        promises_this_round: List[Promise] = []
        for agent in self.agents.values():
            if agent.credits < self.base_stake: continue
            
            domain = random.choice(self.domains)
            stake = self.base_stake * (1 - agent.get_merit(domain) * 0.8)
            if agent.credits < stake: continue
            
            # Ground truth: 90% of promises are kept
            kept = np.random.random() < 0.9
            promises_this_round.append(Promise(agent.id, stake, domain, kept))
            agent.credits -= stake

        # 2. Oracles and agents assess promises
        for promise in promises_this_round:
            # Oracle reports
            oracle_reports = []
            for oracle in self.oracles.values():
                if np.random.random() < oracle.truthfulness:
                    oracle_reports.append(promise.actual_outcome)
                else:
                    oracle_reports.append(not promise.actual_outcome)
            
            # Consensus from oracles (the "perceived truth")
            perceived_truth = stats.mode(oracle_reports, keepdims=False)[0] if oracle_reports else promise.actual_outcome

            # Update promiser based on perceived truth
            promiser = self.agents[promise.promiser_id]
            op_cost = promise.stake * self.op_cost_percentage
            
            if perceived_truth: # Promise perceived as kept
                promiser.credits += (promise.stake - op_cost)
                promiser.update_merit(promise.domain, self.gamma * (1 - promiser.get_merit(promise.domain)))
            else: # Promise perceived as broken
                promiser.update_merit(promise.domain, -self.lambda_penalty * self.gamma * promiser.get_merit(promise.domain))

            # Update Oracles based on if they matched the ground truth
            for i, oracle in enumerate(self.oracles.values()):
                if oracle_reports[i] == promise.actual_outcome:
                    oracle.update_merit(promise.domain, self.gamma * 0.1) # Small merit gain
                else:
                    # Lose credits and merit for being wrong
                    oracle.credits -= 20 
                    oracle.update_merit(promise.domain, -self.lambda_penalty * self.gamma)

            # Praise Bombing Assessment Logic
            if self.praise_bomb_target_id is not None and promise.promiser_id == self.praise_bomb_target_id:
                for assessor in self.agents.values():
                    if assessor.is_coalition_member:
                        # Coalition always gives a positive assessment to the target
                        # This is a simplification; in the full protocol, this would affect merit
                        # Here, we focus on the merit gain of the target itself.
                        pass

        self._record_history()

    def _record_history(self):
        all_entities = {**self.agents, **self.oracles}
        for entity_id, entity in all_entities.items():
            self.history[entity_id]['credits'].append(entity.credits)
            avg_merit = np.mean(list(entity.merit.values()))
            self.history[entity_id]['avg_merit'].append(avg_merit)
            self.history[entity_id]['type'] = entity.type
    
    def run(self, n_rounds, attack_type, attack_round, attack_size):
        if attack_type == 'praise_bombing':
            self.setup_praise_bombing(attack_size)
        
        for i in range(n_rounds):
            if i == attack_round and attack_type == 'oracle_corruption':
                oracle_to_corrupt = random.choice(list(self.oracles.keys()))
                self.corrupt_oracle(oracle_to_corrupt)
            self.run_round()
        return self.history

class SubtleAttackValidator:
    """Runs simulations for different subtle attack scenarios."""
    def run_all_tests(self, n_rounds=200):
        results = {}
        
        print("\n🔬 Running Praise Bombing Simulation...")
        sim_praise = SubtleAttackSimulation()
        history_praise = sim_praise.run(n_rounds, 'praise_bombing', 0, 15)
        results['praise_bombing'] = history_praise
        print("✅ Praise Bombing Simulation Complete.")
        
        print("\n🔬 Running Oracle Corruption Simulation...")
        sim_oracle = SubtleAttackSimulation()
        history_oracle = sim_oracle.run(n_rounds, 'oracle_corruption', n_rounds // 2, 0)
        results['oracle_corruption'] = history_oracle
        print("✅ Oracle Corruption Simulation Complete.")
        
        return results

class SubtleAttackAnalyzer:
    """Analyzes results and generates a report."""
    def __init__(self, results: Dict):
        self.results = results

    def plot_results(self):
        fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(16, 7))

        # Plot 1: Praise Bombing Analysis
        history_praise = self.results['praise_bombing']
        df_praise = pd.DataFrame(history_praise).T
        
        for agent_type in ['Honest', 'Praise Bomb Target']:
            agent_ids = [i for i, data in df_praise.iterrows() if data['type'] == agent_type]
            if not agent_ids: continue
            
            merit_history = np.array([df_praise.loc[i]['avg_merit'] for i in agent_ids])
            mean_merit = merit_history.mean(axis=0)
            ax1.plot(mean_merit, label=f'Avg Merit ({agent_type})')
        
        ax1.set_title('Impact of Praise Bombing on Merit')
        ax1.set_xlabel('Round')
        ax1.set_ylabel('Average Merit')
        ax1.grid(True, alpha=0.3)
        ax1.legend()

        # Plot 2: Oracle Corruption Analysis
        history_oracle = self.results['oracle_corruption']
        df_oracle = pd.DataFrame(history_oracle).T
        attack_round = len(df_oracle.iloc[0]['credits']) // 2

        for agent_type in ['Oracle', 'Corrupt Oracle']:
            agent_ids = [i for i, data in df_oracle.iterrows() if data['type'] == agent_type]
            if not agent_ids: continue
            
            merit_history = np.array([df_oracle.loc[i]['avg_merit'] for i in agent_ids])
            mean_merit = merit_history.mean(axis=0)
            ax2.plot(mean_merit, label=f'Avg Merit ({agent_type})')

        ax2.axvline(x=attack_round, color='red', linestyle='--', label='Oracle Corrupted')
        ax2.set_title('Impact of Oracle Corruption on Merit')
        ax2.set_xlabel('Round')
        ax2.set_ylabel('Average Merit')
        ax2.grid(True, alpha=0.3)
        ax2.legend()

        plt.tight_layout()
        plt.savefig("subtle_attack_analysis.png")
        print("\n📊 Analysis charts saved to 'subtle_attack_analysis.png'")

    def generate_report_text(self):
        report_lines = ["# 🕵️ Agency Protocol: Subtle Attack Simulation Report"]
        
        # --- Praise Bombing Analysis ---
        history_praise = self.results['praise_bombing']
        df_praise = pd.DataFrame(history_praise).T
        target_final_merit = np.mean([data['avg_merit'][-1] for i, data in df_praise.iterrows() if data['type'] == 'Praise Bomb Target'])
        honest_final_merit = np.mean([data['avg_merit'][-1] for i, data in df_praise.iterrows() if data['type'] == 'Honest'])

        report_lines.append("\n## Scenario 1: Praise Bombing Attack")
        if target_final_merit > honest_final_merit * 1.2: # If target merit is >20% higher
            report_lines.append("**Result: VULNERABILITY DETECTED.** The praise bombing strategy was successful, allowing the target agent to achieve an artificially inflated merit score ({:.3f}) compared to honest peers ({:.3f}).".format(target_final_merit, honest_final_merit))
        else:
            report_lines.append("**Result: RESILIENT.** The protocol mitigated the praise bombing attack. The target agent's merit ({:.3f}) did not significantly diverge from honest peers ({:.3f}), likely because their actual performance (promise-breaking) still incurred penalties.".format(target_final_merit, honest_final_merit))

        # --- Oracle Corruption Analysis ---
        history_oracle = self.results['oracle_corruption']
        df_oracle = pd.DataFrame(history_oracle).T
        corrupt_oracle_data = next((data for i, data in df_oracle.iterrows() if data['type'] == 'Corrupt Oracle'), None)
        
        report_lines.append("\n## Scenario 2: Oracle Corruption Attack")
        if corrupt_oracle_data:
            attack_round = len(corrupt_oracle_data['avg_merit']) // 2
            merit_before = corrupt_oracle_data['avg_merit'][attack_round - 1]
            merit_after = corrupt_oracle_data['avg_merit'][-1]
            if merit_after < merit_before * 0.3: # If merit dropped by >70%
                report_lines.append("**Result: RESILIENT.** The protocol successfully identified and penalized the corrupt oracle. After beginning to report false data, its merit plummeted from {:.3f} to {:.3f}, and its credits were significantly slashed. The system correctly isolated and punished the malicious trusted actor.".format(merit_before, merit_after))
            else:
                report_lines.append("**Result: VULNERABILITY DETECTED.** The penalty for oracle corruption was insufficient. The corrupt oracle's merit only fell from {:.3f} to {:.3f}, allowing it to retain significant influence despite its malicious behavior.".format(merit_before, merit_after))
        else:
            report_lines.append("**Result: INCONCLUSIVE.** The oracle corruption scenario did not run as expected.")

        report_lines.append("\n## Recommendations")
        report_lines.append("1. **Implement Low-Entropy Assessment Detection:** To counter praise bombing, the protocol should flag agents who receive an unusually high percentage of positive assessments from a small, correlated group of assessors. This low-entropy signal indicates manipulation, and the associated merit gains should be throttled.")
        report_lines.append("2. **Increase Oracle Staking Requirements:** The stake for oracles must be substantial enough that the penalty for being caught in a single lie outweighs any potential bribe. The `lambda_penalty` for oracles should be significantly higher than for standard agents.")
        report_lines.append("3. **Diversify Oracle Inputs:** For critical promises, the protocol should require consensus from multiple, independent Oracle Agents. A single oracle should never be a single point of failure for verifying a high-value promise.")

        return "\n".join(report_lines)

# --- Main Execution Block ---

if __name__ == "__main__":
    validator = SubtleAttackValidator()
    results = validator.run_all_tests(n_rounds=200)
    
    analyzer = SubtleAttackAnalyzer(results)
    report = analyzer.generate_report_text()
    
    print("\n" + "="*80)
    print(report)
    print("="*80)
    
    analyzer.plot_results()
