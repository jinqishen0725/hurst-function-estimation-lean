from pathlib import Path
s=Path('Hurst/ActualMemoryMainline.lean').read_text()
s=s[s.index('theorem hurstHolder_q1_conditional_memory_mainline'):s.index('\nend Hurst')]
s=s.replace('hurstHolder_q1_conditional_memory_mainline','hurstHolder_q1_conditional_weighted_memory_mainline').replace('(δ₁ δ₂ A R : ℕ → ℝ)','(δ₁ δ₂ A : ℕ → ℝ)')
a=s.index('    (hrows :');b=s.index('    (htail :',a);s=s[:a]+s[b:]
energy='(∑ i,∑ j,|localPolynomialWeights r n 1 (δ₂ n) t i| * |localPolynomialWeights r n 1 (δ₂ n) t j| *\n      |featureCorrelation (gridObservationFeatures n (midpointSampleHurst f hf.1 n))\n        (gridDifferenceCoefficients n i) (gridDifferenceCoefficients n j)|^4)'
s=s.replace('(A n)^2*R n*∑ i,localPolynomialWeights r n 1 (δ₂ n) t i^2','(A n)^2*'+energy)
s=s.replace('featureGaussian_log_limit_of_quadratic_limit P\' (fun n => n-1) v','featureGaussian_log_limit_of_quadratic_weighted_limit P\' (fun n => Fin (n-1)) v')
s=s.replace('gridDifferenceCoefficients A R Z hfeat hrows htail hquad','gridDifferenceCoefficients A Z hfeat htail hquad')
Path('.scratch/ActualWeightedMemoryMainline.lean').write_text('import Hurst.ActualMemoryMainline\nimport Hurst.WeightedQuadraticLimit\n\nnoncomputable section\nopen Set MeasureTheory ProbabilityTheory Filter\nopen scoped Topology RealInnerProductSpace\nnamespace Hurst\n\n'+s+'\nend Hurst\n')
