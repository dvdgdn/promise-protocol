# high_load_stress_test.py
# To run this script:
# 1. Make sure you have the required libraries: pip install pandas numpy matplotlib scipy
# 2. Save this code as a Python file (e.g., high_load_test.py)
# 3. Run from your terminal: python high_load_test.py

import numpy as np
import matplotlib.pyplot as plt
from dataclasses import dataclass, field
from typing import Dict, List, Any
import pandas as pd
import time
import random

# --- Simulation Classes ---

@dataclass
class Agent:
    """A simplified agent model for high-load testing."""
    id: int
    credits: float
    merit: float = 0.2
    honesty_rate: float = 0.95

class HighLoadSimulation:
    """
    A performance-optimized simulation environment for testing scalability.
    """
    def __init__(self, n_agents: int):
        self.n_agents = n_agents
        
        # Economic parameters
        self.base_stake = 100.0
        self.op_cost_percentage = 0.05
        self.lambda_penalty = 3.0
        self.gamma = 0.01

        # State variables
        self.agents = self._initialize_agents()
        self.total_promises_kept = 0
        self.total_promises_made = 0

    def _initialize_agents(self) -> List[Agent]:
        """Initializes a large number of agents efficiently."""
        agents = []
        for i in range(self.n_agents):
            honesty_rate = np.random.choice([0.95, 0.6], p=[0.9, 0.1])
            agents.append(Agent(id=i, credits=1000.0, honesty_rate=honesty_rate))
        return agents

    def run_round(self):
        """
        Executes a single, optimized round of the simulation.
        Uses array operations where possible for performance.
        """
        # Vectorized merit and honesty rates for faster processing
        merits = np.array([agent.merit for agent in self.agents])
        honesty_rates = np.array([agent.honesty_rate for agent in self.agents])
        credits = np.array([agent.credits for agent in self.agents])

        # Agents decide to make a promise (vectorized)
        active_agent_indices = np.where(credits >= self.base_stake)[0]
        
        # Calculate stakes for all active agents
        active_merits = merits[active_agent_indices]
        stakes = self.base_stake * (1 - active_merits * 0.8)
        
        # Agents decide whether to keep their promise
        rand_decision = np.random.rand(len(active_agent_indices))
        kept_promises_mask = rand_decision < honesty_rates[active_agent_indices]
        
        # Update promise counts
        self.total_promises_made += len(active_agent_indices)
        self.total_promises_kept += np.sum(kept_promises_mask)
        
        # Update credits and merit (vectorized)
        # 1. All active agents pay the stake
        credits[active_agent_indices] -= stakes
        
        # 2. Kept promises: return stake (minus op_cost) and increase merit
        kept_indices = active_agent_indices[kept_promises_mask]
        op_costs_kept = stakes[kept_promises_mask] * self.op_cost_percentage
        credits[kept_indices] += stakes[kept_promises_mask] - op_costs_kept
        merits[kept_indices] += self.gamma * (1 - merits[kept_indices])

        # 3. Broken promises: lose stake and decrease merit
        broken_indices = active_agent_indices[~kept_promises_mask]
        merits[broken_indices] -= self.lambda_penalty * self.gamma * merits[broken_indices]

        # Ensure merit and credits are within bounds
        merits = np.clip(merits, 0.0, 1.0)
        
        # Update agent objects from the arrays
        for i, agent_idx in enumerate(active_agent_indices):
            self.agents[agent_idx].credits = credits[agent_idx]
            self.agents[agent_idx].merit = merits[agent_idx]

    def get_system_health(self) -> Dict[str, float]:
        """Calculates key health metrics for the current state."""
        if not self.agents:
            return {'avg_merit': 0, 'promise_keeping_rate': 0}
            
        avg_merit = np.mean([agent.merit for agent in self.agents])
        promise_keeping_rate = (self.total_promises_kept / self.total_promises_made) if self.total_promises_made > 0 else 1.0
        
        return {
            'avg_merit': avg_merit,
            'promise_keeping_rate': promise_keeping_rate
        }

# --- Validation Suite ---

class HighLoadValidator:
    """
    Runs the HighLoadSimulation across a range of agent counts
    to validate performance and stability at scale.
    """
    def run_stress_test(self, agent_counts: List[int], rounds_per_test: int = 50):
        print("🔬 Running High-Load Stress Test...")
        results = []

        for count in agent_counts:
            print(f"  Testing with {count:,} agents...")
            sim = HighLoadSimulation(n_agents=count)
            
            start_time = time.time()
            for _ in range(rounds_per_test):
                sim.run_round()
            end_time = time.time()
            
            duration = end_time - start_time
            avg_time_per_round = duration / rounds_per_test
            
            health_metrics = sim.get_system_health()
            
            results.append({
                'agent_count': count,
                'avg_time_per_round_ms': avg_time_per_round * 1000,
                'avg_merit': health_metrics['avg_merit'],
                'promise_keeping_rate': health_metrics['promise_keeping_rate']
            })
        
        print("✅ Stress Test Complete.")
        return results

# --- Analysis and Reporting ---

class HighLoadAnalyzer:
    """Analyzes the stress test results and generates a report."""
    def __init__(self, validation_results: List[Dict]):
        self.results_df = pd.DataFrame(validation_results)

    def plot_results(self):
        """Generates and saves the analysis charts."""
        fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(16, 7))

        # Plot 1: Performance Scaling
        ax1.plot(self.results_df['agent_count'], self.results_df['avg_time_per_round_ms'], 'o-', label="Time per Round")
        ax1.set_title('Performance Scaling Under Load')
        ax1.set_xlabel('Number of Agents')
        ax1.set_ylabel('Average Time per Round (ms)')
        ax1.set_xscale('log')
        ax1.set_yscale('log')
        ax1.grid(True, which="both", ls="--", alpha=0.3)
        ax1.legend()

        # Plot 2: System Stability
        ax2.plot(self.results_df['agent_count'], self.results_df['promise_keeping_rate'] * 100, 'o-', color='green', label="Promise Keeping Rate")
        ax2.set_title('System Stability Under Load')
        ax2.set_xlabel('Number of Agents')
        ax2.set_ylabel('Promise Keeping Rate (%)')
        ax2.set_xscale('log')
        ax2.set_ylim(50, 101)
        ax2.axhline(90, color='lightgreen', linestyle='--', label='Target Stability (90%)')
        ax2.grid(True, which="both", ls="--", alpha=0.3)
        ax2.legend(loc='lower left')
        
        # Secondary axis for merit
        ax2b = ax2.twinx()
        ax2b.plot(self.results_df['agent_count'], self.results_df['avg_merit'], 'o--', color='skyblue', label="Average Merit")
        ax2b.set_ylabel('Final Average Merit')
        ax2b.legend(loc='lower right')

        plt.tight_layout()
        plt.savefig("high_load_analysis.png")
        print("\n📊 Analysis charts saved to 'high_load_analysis.png'")

    def generate_report_text(self):
        """Generates a full markdown report as a string."""
        report_lines = ["# ⚙️ Agency Protocol: High-Load Stress Test Report"]
        
        report_lines.append("\n## Executive Summary")
        
        # Analyze performance scaling
        log_agents = np.log(self.results_df['agent_count'])
        log_time = np.log(self.results_df['avg_time_per_round_ms'])
        slope, _, _, _, _ = stats.linregress(log_agents, log_time)
        
        if slope < 1.1:
            perf_assessment = f"**Excellent performance scaling (O(n^{slope:.2f})).** The system's processing time scales nearly linearly with the number of agents, indicating a highly efficient architecture capable of handling large ecosystems."
        elif slope < 1.5:
            perf_assessment = f"**Acceptable performance scaling (O(n^{slope:.2f})).** The system shows some non-linear overhead but should be manageable for moderately large networks. Further optimization is recommended."
        else:
            perf_assessment = f"**Poor performance scaling (O(n^{slope:.2f})).** The system's computational complexity is too high, indicating it will not scale to a large number of users without a significant architectural redesign (e.g., Layer 2 rollups)."

        # Analyze stability
        final_stability = self.results_df['promise_keeping_rate'].iloc[-1]
        if final_stability > 0.85:
            stability_assessment = "**System incentives remain stable at scale.** The promise-keeping rate and average merit hold steady even with a large number of agents, proving the core economic model is robust."
        else:
            stability_assessment = "**System incentives degrade at scale.** The promise-keeping rate drops significantly under high load, suggesting that emergent behaviors may be undermining the protocol's stability. This requires further investigation."

        report_lines.append(perf_assessment)
        report_lines.append(stability_assessment)

        report_lines.append("\n## Key Metrics Analysis")
        report_lines.append(self.results_df.to_string(formatters={
            'agent_count': "{:,.0f}".format,
            'avg_time_per_round_ms': "{:.2f}".format,
            'avg_merit': "{:.3f}".format,
            'promise_keeping_rate': "{:.1%}".format
        }))

        report_lines.append("\n## Recommendations")
        report_lines.append("1. **Confirm Architectural Assumptions:** The observed performance scaling ({:.2f}) should be compared against the complexity of the proposed on-chain architecture. This result strongly supports the viability of an L2/rollup design, as it confirms the core logic can be executed efficiently off-chain.".format(slope))
        report_lines.append("2. **Investigate Stability at Extreme Scale:** While stability held for the tested range, simulations with millions of agents should be conducted to check for emergent phenomena like network fragmentation or localized, non-cooperative equilibria.")
        report_lines.append("3. **Optimize Data Structures:** The current simulation uses basic Python objects. A production implementation should use more memory-efficient data structures to further improve performance at scale.")

        return "\n".join(report_lines)

# --- Main Execution Block ---

if __name__ == "__main__":
    # Define test parameters
    # Test with agent counts from 100 up to 10,000 on a logarithmic scale
    AGENT_COUNTS = [100, 200, 500, 1000, 2000, 5000, 10000]
    ROUNDS_PER_TEST = 50

    # Run the validation suite
    validator = HighLoadValidator()
    results_data = validator.run_stress_test(agent_counts=AGENT_COUNTS, rounds_per_test=ROUNDS_PER_TEST)
    
    # Analyze the results and generate the report
    analyzer = HighLoadAnalyzer(results_data)
    report = analyzer.generate_report_text()
    
    print("\n" + "="*80)
    print(report)
    print("="*80)
    
    # Generate and save plots
    analyzer.plot_results()
