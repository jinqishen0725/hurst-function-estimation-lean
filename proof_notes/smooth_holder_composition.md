# 原Hölder类与光滑校准函数的复合

设p≥2，m=⌈p⌉−1，α=p−m∈(0,1]。固定0<a≤H≤b<1。以下直接证明用于q=2校准项φ(h)=log(4−2^(2h))；不提高局部多项式次数。

原函数类及值域界已给出各阶导数的统一界。对每个k≤m，还可统一得到

```
|H^(k)(x)−H^(k)(y)|≤C|x−y|^α.
```

当k<⌊p⌋时，用已有Lipschitz界及区间长度≤1；当k=⌊p⌋时直接用原Hölder条件。整数p时m=p−1，故只需原类已经推出的第p−1阶导数Lipschitz界，不增加H^(p)连续的假设。由此H属于C^m。

φ在[a,b]附近光滑，有限阶导数的绝对值和Lipschitz常数统一有界。复用固定版本mathlib中 `iteratedDeriv_comp_eq_sum_orderedFinpartition`，把(φ∘H)^(m)写成有限和；每一项由一个φ的导数和若干H的导数相乘。有限乘积差的望远镜分解给出每项的同阶Hölder界，故

```
|(φ∘H)^(m)(x)−(φ∘H)^(m)(y)|≤K|x−y|^α.
```

已有Taylor余项定理于是给出

```
|(φ∘H)(y)−Taylor_m(φ∘H;x,y)|≤K'|x−y|^p.
```

常数位于函数量词之前，对整个固定原Hölder类统一。局部多项式权重的精确矩条件消掉m阶Taylor多项式，得到O(δ^p)平滑偏差；端点用已验证的权重连续性和连续延拓处理。

Lean证据：HolderJets、SmoothJetBounds、FiniteProductBounds、JetComposition、HolderComposition。最后的局部平滑连接与风险应用继续在后续模块核验。

第十七阶段已将本余项接入实际局部多项式偏差、q=2均值方差与全域平方Ls风险，覆盖全部p≥2和1≤s≤2。见Hurst/HolderQ2LpRisk.lean。
