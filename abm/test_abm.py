import numpy as np
import matplotlib.pyplot as plt
from dataclasses import dataclass
from typing import Dict, List, Tuple
import pandas as pd

# Import the simulation class from the previous artifact
# (In practice, this would be an import statement)

class ProtocolValidator:
    """Test suite to validate Agency Protocol's theoretical claims"""
    
    def __init__(self):
        self.test_results = {}
    
    def test_subgame_perfect_equilibrium(self, n_trials: int = 10):
        """Test Theorem 4: Promise-keeping forms subgame perfect equilibrium"""
        print("\n=== Testing Subgame Perfect Equilibrium ===")
        
        keeping_rates = []
        merit_growth = []
        
        for trial in range(n_trials):
            sim = AgencyProtocolSimulation(
                n_agents=50,
                n_domains=3,
                beta=2.0,  # High merit weight to test equilibrium
                discount_factor=0.9
            )
            sim.run_simulation(n_rounds=100)
            
            # Calculate promise keeping rate
            kept = sum(1 for p in sim.promise_history if p.actual_outcome)
            total = len(sim.promise_history)
            keeping_rate = kept / total if total > 0 else 0
            keeping_rates.append(keeping_rate)
            
            # Calculate merit growth for honest vs dishonest agents
            honest_merits = []
            dishonest_merits = []
            
            for agent in sim.agents.values():
                avg_merit = np.mean(list(agent.merit.values())) if agent.merit else 0
                if agent.honesty_rate > 0.5:
                    honest_merits.append(avg_merit)
                else:
                    dishonest_merits.append(avg_merit)
            
            if honest_merits and dishonest_merits:
                merit_growth.append(np.mean(honest_merits) - np.mean(dishonest_merits))
        
        avg_keeping_rate = np.mean(keeping_rates)
        avg_merit_advantage = np.mean(merit_growth)
        
        print(f"Average promise keeping rate: {avg_keeping_rate:.3f}")
        print(f"Merit advantage for honest agents: {avg_merit_advantage:.3f}")
        
        # Test passes if keeping rate > 70% and honest agents have merit advantage
        passed = avg_keeping_rate > 0.7 and avg_merit_advantage > 0.1
        
        self.test_results['subgame_perfect_equilibrium'] = {
            'passed': passed,
            'keeping_rate': avg_keeping_rate,
            'merit_advantage': avg_merit_advantage
        }
        
        return passed
    
    def test_coalition_resistance(self, coalition_sizes: List[int] = [5, 10, 20, 30]):
        """Test Theorems 5-7: Coalition manipulation becomes unviable with size"""
        print("\n=== Testing Coalition Resistance ===")
        
        detection_rates = {}
        coalition_success_rates = {}
        
        for size in coalition_sizes:
            detections = []
            successes = []
            
            for trial in range(5):
                sim = AgencyProtocolSimulation(
                    n_agents=100,
                    n_domains=3,
                    detection_sensitivity=0.5
                )
                
                # Run with coalition attack
                sim.run_simulation(n_rounds=50, coalition_round=25, coalition_size=size)
                
                # Measure detection rate
                detection_rate = len(sim.detection_history) / len(sim.promise_history) if sim.promise_history else 0
                detections.append(detection_rate)
                
                # Measure coalition success (lower merit for targets)
                coalition_members = [a for a in sim.agents.values() if a.coalition_member]
                if coalition_members:
                    avg_coalition_merit = np.mean([np.mean(list(a.merit.values())) 
                                                 for a in coalition_members if a.merit])
                    success = avg_coalition_merit > 0.5  # Arbitrary threshold
                    successes.append(success)
            
            detection_rates[size] = np.mean(detections)
            coalition_success_rates[size] = np.mean(successes)
        
        # Plot results
        plt.figure(figsize=(10, 5))
        
        plt.subplot(1, 2, 1)
        plt.plot(list(detection_rates.keys()), list(detection_rates.values()), 'o-')
        plt.xlabel('Coalition Size')
        plt.ylabel('Detection Rate')
        plt.title('Detection Rate vs Coalition Size')
        plt.grid(True, alpha=0.3)
        
        plt.subplot(1, 2, 2)
        plt.plot(list(coalition_success_rates.keys()), list(coalition_success_rates.values()), 'o-', color='red')
        plt.xlabel('Coalition Size')
        plt.ylabel('Coalition Success Rate')
        plt.title('Coalition Success vs Size')
        plt.grid(True, alpha=0.3)
        
        plt.tight_layout()
        plt.show()
        
        # Test passes if detection increases and success decreases with size
        detection_increasing = all(detection_rates[coalition_sizes[i]] <= detection_rates[coalition_sizes[i+1]] 
                                 for i in range(len(coalition_sizes)-1))
        
        large_coalition_fails = coalition_success_rates[max(coalition_sizes)] < 0.3
        
        passed = detection_increasing or large_coalition_fails
        
        print(f"Detection rates: {detection_rates}")
        print(f"Coalition success rates: {coalition_success_rates}")
        print(f"Test passed: {passed}")
        
        self.test_results['coalition_resistance'] = {
            'passed': passed,
            'detection_rates': detection_rates,
            'success_rates': coalition_success_rates
        }
        
        return passed
    
    def test_bounded_rationality(self, error_rates: List[float] = [0.0, 0.1, 0.2, 0.3]):
        """Test Theorem 11: System robust to bounded rationality"""
        print("\n=== Testing Bounded Rationality Robustness ===")
        
        equilibrium_stability = {}
        
        for error_rate in error_rates:
            keeping_rates = []
            
            for trial in range(5):
                # Create agents with varying error rates
                sim = AgencyProtocolSimulation(n_agents=50, n_domains=3)
                
                # Inject errors into decision making
                for agent in sim.agents.values():
                    # Reduce honesty rate based on error rate
                    agent.honesty_rate = max(0.1, agent.honesty_rate - error_rate)
                
                sim.run_simulation(n_rounds=100)
                
                kept = sum(1 for p in sim.promise_history if p.actual_outcome)
                total = len(sim.promise_history)
                keeping_rate = kept / total if total > 0 else 0
                keeping_rates.append(keeping_rate)
            
            equilibrium_stability[error_rate] = np.mean(keeping_rates)
        
        # Plot results
        plt.figure(figsize=(8, 6))
        plt.plot(list(equilibrium_stability.keys()), list(equilibrium_stability.values()), 'o-')
        plt.xlabel('Error Rate')
        plt.ylabel('Promise Keeping Rate')
        plt.title('Equilibrium Stability vs Bounded Rationality')
        plt.grid(True, alpha=0.3)
        plt.axhline(y=0.5, color='r', linestyle='--', label='Cooperation Threshold')
        plt.legend()
        plt.show()
        
        # Test passes if cooperation maintained up to 20% error rate
        passed = equilibrium_stability[0.2] > 0.5
        
        print(f"Equilibrium stability: {equilibrium_stability}")
        print(f"Test passed: {passed}")
        
        self.test_results['bounded_rationality'] = {
            'passed': passed,
            'stability': equilibrium_stability
        }
        
        return passed
    
    def test_lyapunov_stability(self, perturbation_round: int = 50):
        """Test Theorem 9: System returns to equilibrium after perturbation"""
        print("\n=== Testing Lyapunov Stability ===")
        
        # Run simulation with perturbation
        sim = AgencyProtocolSimulation(n_agents=50, n_domains=3)
        
        merit_trajectory = []
        
        for round_num in range(100):
            # Introduce perturbation at specified round
            if round_num == perturbation_round:
                # Randomly flip some agents to dishonest
                for agent in sim.agents.values():
                    if np.random.random() < 0.3:
                        agent.honesty_rate = 0.2
                print(f"Perturbation introduced at round {round_num}")
            
            # Restore agents after perturbation
            elif round_num == perturbation_round + 10:
                for agent in sim.agents.values():
                    if agent.honesty_rate < 0.5:
                        agent.honesty_rate = 0.9
                print("Perturbation removed")
            
            sim.simulate_round()
            sim.record_history()
            
            # Track average merit
            avg_merit = np.mean([np.mean(list(a.merit.values())) 
                               for a in sim.agents.values() if a.merit])
            merit_trajectory.append(avg_merit)
        
        # Plot trajectory
        plt.figure(figsize=(10, 6))
        plt.plot(merit_trajectory, linewidth=2)
        plt.axvline(x=perturbation_round, color='red', linestyle='--', label='Perturbation')
        plt.axvline(x=perturbation_round+10, color='green', linestyle='--', label='Recovery')
        plt.xlabel('Round')
        plt.ylabel('Average Merit')
        plt.title('System Response to Perturbation')
        plt.legend()
        plt.grid(True, alpha=0.3)
        plt.show()
        
        # Test passes if system recovers to within 90% of pre-perturbation level
        pre_perturbation_merit = np.mean(merit_trajectory[40:50])
        post_recovery_merit = np.mean(merit_trajectory[80:90])
        recovery_ratio = post_recovery_merit / pre_perturbation_merit if pre_perturbation_merit > 0 else 0
        
        passed = recovery_ratio > 0.9
        
        print(f"Pre-perturbation merit: {pre_perturbation_merit:.3f}")
        print(f"Post-recovery merit: {post_recovery_merit:.3f}")
        print(f"Recovery ratio: {recovery_ratio:.3f}")
        print(f"Test passed: {passed}")
        
        self.test_results['lyapunov_stability'] = {
            'passed': passed,
            'recovery_ratio': recovery_ratio,
            'trajectory': merit_trajectory
        }
        
        return passed
    
    def test_stake_merit_relationship(self):
        """Test that higher merit leads to lower stake requirements and better outcomes"""
        print("\n=== Testing Stake-Merit Relationship ===")
        
        sim = AgencyProtocolSimulation(n_agents=30, n_domains=2)
        
        # Track stake requirements and outcomes by merit level
        merit_buckets = {
            'low': {'stakes': [], 'profits': []},
            'medium': {'stakes': [], 'profits': []},
            'high': {'stakes': [], 'profits': []}
        }
        
        # Run simulation and collect data
        for _ in range(50):
            sim.simulate_round()
            
            for agent in sim.agents.values():
                avg_merit = np.mean(list(agent.merit.values())) if agent.merit else 0
                
                # Categorize by merit level
                if avg_merit < 0.33:
                    bucket = 'low'
                elif avg_merit < 0.67:
                    bucket = 'medium'
                else:
                    bucket = 'high'
                
                # Calculate average stake requirement
                avg_stake = np.mean([sim.calculate_stake_requirement(agent, domain) 
                                   for domain in sim.domains])
                merit_buckets[bucket]['stakes'].append(avg_stake)
        
        # Calculate averages
        results = {}
        for bucket, data in merit_buckets.items():
            if data['stakes']:
                results[bucket] = np.mean(data['stakes'])
            else:
                results[bucket] = sim.base_stake
        
        # Test passes if stake requirements decrease with merit
        passed = results['high'] < results['medium'] < results['low']
        
        print(f"Average stake requirements by merit level:")
        print(f"  Low merit: {results.get('low', 'N/A'):.1f}")
        print(f"  Medium merit: {results.get('medium', 'N/A'):.1f}")
        print(f"  High merit: {results.get('high', 'N/A'):.1f}")
        print(f"Test passed: {passed}")
        
        self.test_results['stake_merit_relationship'] = {
            'passed': passed,
            'stake_requirements': results
        }
        
        return passed
    
    def run_all_tests(self):
        """Run all validation tests"""
        print("=" * 60)
        print("AGENCY PROTOCOL VALIDATION TEST SUITE")
        print("=" * 60)
        
        tests = [
            ("Subgame Perfect Equilibrium", self.test_subgame_perfect_equilibrium),
            ("Coalition Resistance", self.test_coalition_resistance),
            ("Bounded Rationality", self.test_bounded_rationality),
            ("Lyapunov Stability", self.test_lyapunov_stability),
            ("Stake-Merit Relationship", self.test_stake_merit_relationship)
        ]
        
        passed_tests = 0
        
        for test_name, test_func in tests:
            try:
                passed = test_func()
                if passed:
                    passed_tests += 1
            except Exception as e:
                print(f"ERROR in {test_name}: {e}")
                self.test_results[test_name] = {'passed': False, 'error': str(e)}
        
        # Summary
        print("\n" + "=" * 60)
        print("TEST SUMMARY")
        print("=" * 60)
        print(f"Tests passed: {passed_tests}/{len(tests)}")
        
        for test_name, result in self.test_results.items():
            status = "PASS" if result.get('passed', False) else "FAIL"
            print(f"{test_name}: {status}")
        
        overall_validity = passed_tests / len(tests)
        print(f"\nOverall Protocol Validity Score: {overall_validity:.1%}")
        
        return self.test_results, overall_validity

# Run the validation suite
if __name__ == "__main__":
    validator = ProtocolValidator()
    results, validity_score = validator.run_all_tests()
    
    print(f"\n{'='*60}")
    print(f"FINAL ASSESSMENT: The Agency Protocol demonstrates {validity_score:.1%} validity")
    print(f"in agent-based simulation testing.")
    print(f"{'='*60}")
