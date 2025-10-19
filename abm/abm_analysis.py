"""
Agency Protocol Simulation Analysis
===================================

This script analyzes the results from our agent-based model to provide
insights about the Agency Protocol's real-world viability.
"""

import numpy as np
import matplotlib.pyplot as plt
from typing import Dict, List, Tuple

class ProtocolAnalyzer:
    """Analyze simulation results to assess protocol viability"""
    
    def __init__(self):
        self.findings = {}
        
    def analyze_equilibrium_emergence(self, keeping_rate: float, merit_advantage: float) -> Dict:
        """Analyze whether cooperative equilibrium emerges as predicted"""
        
        analysis = {
            'theoretical_claim': 'Promise-keeping forms subgame perfect equilibrium',
            'observed_keeping_rate': keeping_rate,
            'merit_advantage_honest': merit_advantage,
            'assessment': ''
        }
        
        if keeping_rate > 0.8:
            analysis['assessment'] = 'STRONG SUPPORT: High promise-keeping rate indicates cooperative equilibrium'
        elif keeping_rate > 0.6:
            analysis['assessment'] = 'MODERATE SUPPORT: Cooperation emerges but not as dominant as theory predicts'
        else:
            analysis['assessment'] = 'WEAK SUPPORT: Cooperation struggles to emerge'
            
        self.findings['equilibrium'] = analysis
        return analysis
    
    def analyze_coalition_dynamics(self, detection_rates: Dict[int, float], 
                                 success_rates: Dict[int, float]) -> Dict:
        """Analyze coalition resistance properties"""
        
        # Check if detection increases with size
        sizes = sorted(detection_rates.keys())
        detection_trend = np.polyfit(sizes, 
                                    [detection_rates[s] for s in sizes], 1)[0]
        success_trend = np.polyfit(sizes, 
                                  [success_rates[s] for s in sizes], 1)[0]
        
        analysis = {
            'theoretical_claim': 'Larger coalitions face exponentially increasing detection',
            'detection_trend': 'increasing' if detection_trend > 0 else 'decreasing',
            'success_trend': 'decreasing' if success_trend < 0 else 'increasing',
            'largest_coalition_success': success_rates[max(sizes)],
            'assessment': ''
        }
        
        if detection_trend > 0 and success_trend < 0:
            analysis['assessment'] = 'STRONG SUPPORT: Coalition resistance works as designed'
        elif detection_trend > 0 or success_trend < 0:
            analysis['assessment'] = 'PARTIAL SUPPORT: Some resistance mechanisms working'
        else:
            analysis['assessment'] = 'CONCERN: Coalition resistance may be insufficient'
            
        self.findings['coalition'] = analysis
        return analysis
    
    def analyze_stability(self, recovery_ratio: float, merit_trajectory: List[float]) -> Dict:
        """Analyze Lyapunov stability properties"""
        
        # Calculate volatility post-recovery
        post_recovery = merit_trajectory[-20:]
        volatility = np.std(post_recovery) / np.mean(post_recovery) if post_recovery else 0
        
        analysis = {
            'theoretical_claim': 'System exhibits Lyapunov stability',
            'recovery_ratio': recovery_ratio,
            'post_recovery_volatility': volatility,
            'assessment': ''
        }
        
        if recovery_ratio > 0.95 and volatility < 0.1:
            analysis['assessment'] = 'STRONG SUPPORT: System quickly returns to stable equilibrium'
        elif recovery_ratio > 0.8:
            analysis['assessment'] = 'MODERATE SUPPORT: System recovers but may take time'
        else:
            analysis['assessment'] = 'WEAK SUPPORT: Recovery is incomplete or unstable'
            
        self.findings['stability'] = analysis
        return analysis
    
    def analyze_parameter_sensitivity(self, sim_class) -> Dict:
        """Test sensitivity to key parameters"""
        
        print("\n=== Parameter Sensitivity Analysis ===")
        
        # Test different parameter combinations
        parameter_tests = {
            'merit_weight_beta': [0.5, 1.0, 2.0, 4.0],
            'penalty_lambda': [1.5, 2.0, 3.0, 4.0],
            'detection_sensitivity': [0.1, 0.5, 1.0, 2.0]
        }
        
        sensitivity_results = {}
        
        for param_name, values in parameter_tests.items():
            keeping_rates = []
            
            for value in values:
                # Create simulation with modified parameter
                kwargs = {param_name.split('_')[-1]: value}
                sim = sim_class(n_agents=30, n_domains=2, **kwargs)
                sim.run_simulation(n_rounds=50)
                
                # Measure outcome
                kept = sum(1 for p in sim.promise_history if p.actual_outcome)
                total = len(sim.promise_history)
                rate = kept / total if total > 0 else 0
                keeping_rates.append(rate)
            
            sensitivity_results[param_name] = {
                'values': values,
                'keeping_rates': keeping_rates,
                'variance': np.var(keeping_rates)
            }
        
        # Visualize
        fig, axes = plt.subplots(1, 3, figsize=(15, 5))
        
        for idx, (param_name, results) in enumerate(sensitivity_results.items()):
            ax = axes[idx]
            ax.plot(results['values'], results['keeping_rates'], 'o-')
            ax.set_xlabel(param_name.replace('_', ' ').title())
            ax.set_ylabel('Promise Keeping Rate')
            ax.set_title(f'Sensitivity to {param_name.replace("_", " ").title()}')
            ax.grid(True, alpha=0.3)
            ax.set_ylim(0, 1)
        
        plt.tight_layout()
        plt.show()
        
        # Assess robustness
        avg_variance = np.mean([r['variance'] for r in sensitivity_results.values()])
        
        analysis = {
            'parameter_sensitivity': sensitivity_results,
            'average_variance': avg_variance,
            'assessment': 'ROBUST' if avg_variance < 0.05 else 'SENSITIVE'
        }
        
        self.findings['parameters'] = analysis
        return analysis
    
    def generate_recommendations(self) -> List[str]:
        """Generate recommendations based on analysis"""
        
        recommendations = []
        
        # Check equilibrium findings
        if 'equilibrium' in self.findings:
            if 'WEAK' in self.findings['equilibrium']['assessment']:
                recommendations.append(
                    "Consider increasing merit rewards or credit penalties to strengthen cooperative incentives"
                )
        
        # Check coalition findings
        if 'coalition' in self.findings:
            if 'CONCERN' in self.findings['coalition']['assessment']:
                recommendations.append(
                    "Enhance detection mechanisms - consider adding pattern recognition or network analysis"
                )
        
        # Check stability findings
        if 'stability' in self.findings:
            if 'WEAK' in self.findings['stability']['assessment']:
                recommendations.append(
                    "Implement additional stabilization mechanisms like reputation recovery periods"
                )
        
        # Check parameter sensitivity
        if 'parameters' in self.findings:
            if self.findings['parameters']['assessment'] == 'SENSITIVE':
                recommendations.append(
                    "Implement adaptive parameter tuning to maintain stability across different conditions"
                )
        
        # General recommendations
        recommendations.extend([
            "Start with conservative parameters and gradually adjust based on observed behavior",
            "Implement comprehensive monitoring to detect emergent behaviors early",
            "Consider domain-specific parameter tuning rather than one-size-fits-all"
        ])
        
        return recommendations
    
    def generate_report(self, test_results: Dict) -> str:
        """Generate comprehensive analysis report"""
        
        report = """
AGENCY PROTOCOL SIMULATION ANALYSIS REPORT
==========================================

EXECUTIVE SUMMARY
-----------------
"""
        
        # Overall assessment
        passed_tests = sum(1 for r in test_results.values() if r.get('passed', False))
        total_tests = len(test_results)
        validity_score = passed_tests / total_tests
        
        report += f"Overall Validity Score: {validity_score:.1%} ({passed_tests}/{total_tests} tests passed)\n\n"
        
        # Detailed findings
        report += "DETAILED FINDINGS\n"
        report += "-----------------\n\n"
        
        for finding_name, finding in self.findings.items():
            report += f"{finding_name.upper()}:\n"
            for key, value in finding.items():
                if key != 'assessment':
                    report += f"  - {key}: {value}\n"
            report += f"  ASSESSMENT: {finding.get('assessment', 'N/A')}\n\n"
        
        # Key insights
        report += "KEY INSIGHTS\n"
        report += "------------\n"
        
        insights = []
        
        if validity_score > 0.8:
            insights.append("✓ The Agency Protocol demonstrates strong theoretical validity")
            insights.append("✓ Core game-theoretic properties hold under simulation")
        elif validity_score > 0.6:
            insights.append("◐ The Protocol shows promise but needs refinement")
            insights.append("◐ Some mechanisms work well, others need adjustment")
        else:
            insights.append("✗ Significant gaps between theory and simulated behavior")
            insights.append("✗ Major revisions needed before practical deployment")
        
        # Specific insights based on findings
        if self.findings.get('equilibrium', {}).get('merit_advantage_honest', 0) > 0.2:
            insights.append("✓ Merit system effectively rewards honest behavior")
        
        if self.findings.get('coalition', {}).get('largest_coalition_success', 1) < 0.3:
            insights.append("✓ Large coalitions struggle to succeed, validating resistance mechanisms")
        
        for insight in insights:
            report += f"{insight}\n"
        
        # Recommendations
        report += "\nRECOMMENDATIONS\n"
        report += "---------------\n"
        
        recommendations = self.generate_recommendations()
        for i, rec in enumerate(recommendations, 1):
            report += f"{i}. {rec}\n"
        
        # Risk assessment
        report += "\nRISK ASSESSMENT\n"
        report += "---------------\n"
        
        risks = [
            ("Parameter Sensitivity", "Medium" if validity_score > 0.7 else "High"),
            ("Coalition Attacks", "Low" if validity_score > 0.8 else "Medium"),
            ("Emergent Behaviors", "Unknown - requires live testing"),
            ("Scalability", "Unknown - current tests limited to 100 agents")
        ]
        
        for risk, level in risks:
            report += f"- {risk}: {level}\n"
        
        # Conclusion
        report += f"\nCONCLUSION\n"
        report += f"----------\n"
        report += f"The Agency Protocol shows {validity_score:.0%} theoretical validity in simulation. "
        
        if validity_score > 0.8:
            report += "The protocol is ready for limited real-world trials with careful monitoring."
        elif validity_score > 0.6:
            report += "Further refinement and testing are recommended before deployment."
        else:
            report += "Significant design revisions are needed to address identified weaknesses."
        
        return report


# Example usage
if __name__ == "__main__":
    # Create analyzer
    analyzer = ProtocolAnalyzer()
    
    # Example test results (would come from actual simulation)
    example_results = {
        'subgame_perfect_equilibrium': {
            'passed': True,
            'keeping_rate': 0.82,
            'merit_advantage': 0.25
        },
        'coalition_resistance': {
            'passed': True,
            'detection_rates': {5: 0.1, 10: 0.2, 20: 0.4, 30: 0.6},
            'success_rates': {5: 0.6, 10: 0.4, 20: 0.2, 30: 0.1}
        },
        'bounded_rationality': {
            'passed': True,
            'stability': {0.0: 0.85, 0.1: 0.78, 0.2: 0.65, 0.3: 0.45}
        },
        'lyapunov_stability': {
            'passed': True,
            'recovery_ratio': 0.92,
            'trajectory': [0.5] * 100  # Simplified
        },
        'stake_merit_relationship': {
            'passed': True,
            'stake_requirements': {'low': 90, 'medium': 60, 'high': 30}
        }
    }
    
    # Analyze each component
    analyzer.analyze_equilibrium_emergence(
        example_results['subgame_perfect_equilibrium']['keeping_rate'],
        example_results['subgame_perfect_equilibrium']['merit_advantage']
    )
    
    analyzer.analyze_coalition_dynamics(
        example_results['coalition_resistance']['detection_rates'],
        example_results['coalition_resistance']['success_rates']
    )
    
    analyzer.analyze_stability(
        example_results['lyapunov_stability']['recovery_ratio'],
        example_results['lyapunov_stability']['trajectory']
    )
    
    # Generate report
    report = analyzer.generate_report(example_results)
    print(report)
