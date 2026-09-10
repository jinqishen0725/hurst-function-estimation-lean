# Gaussian 偶函数协方差：直接密度证明

用途：补Lean主线中的二阶风险工具。下述直接路线已在GaussianOverlap、GaussianSymmetry、GaussianRotation、GaussianPairLaw、GaussianLogCovariance中完整形式化，GaussianLogRisk进一步给出实际加权方差界。实际mBm相关求和与风险链仍缺，不能据此将风险定理标为完成。它不代替文件19任意高阶矩引理。

令(X,Y)为联合标准Gaussian，相关系数rho。若f、g在标准Gaussian测度gamma下属于L²、均值为0，且g为偶函数，则

\[
|E[f(X)g(Y)]|\le4\rho^2\|f\|_{L^2(\gamma)}\|g\|_{L^2(\gamma)}.
\]

特别地，f=g=log(x²)−E log Z²满足这些条件；全部所需单变量矩已经在GaussianLog中证明。

## 1. 标量密度重叠

对v>0，记

\[
r_v(x)=v^{-1/2}\exp\{(1-v^{-1})x^2/2\}.
\]

它是N(0,v)对gamma的密度。若a,b>0且d=a+b−ab>0，直接相乘并积分得到

\[
\int r_a r_b\,d\gamma=d^{-1/2}.
\]

可令c=ab/d，则c^{-1}=a^{-1}+b^{-1}−1，逐点有r_a r_b= sqrt(c)/(sqrt(a)sqrt(b)) r_c，利用积分r_c=1即可。

## 2. 对角化和对称化

对|rho|<1，令U=(X+Y)/sqrt(2)、V=(X−Y)/sqrt(2)。它们独立，方差分别为1+rho、1−rho。因此相对于两个独立标准Gaussian的乘积测度，密度为

\[
R_\rho(u,v)=r_{1+\rho}(u)r_{1-\rho}(v).
\]

设A(u,v)=f((u+v)/sqrt(2))g((u−v)/sqrt(2))。g为偶函数，所以A(v,u)=A(u,v)。交换两个独立标准Gaussian不改变基准测度，于是

\[
E[f(X)g(Y)]=\int A(S_\rho-1)\,d\gamma^{\otimes2},
\qquad S_\rho=(R_\rho+R_{-\rho})/2.
\]

减去1合法，因为基准测度经该正交变换仍是两个独立标准Gaussian，而f、g均值为0。

第1步的重叠公式给出

\[
\int R_\rho^2=\frac1{1-\rho^2},\quad
\int R_\rho R_{-\rho}=\frac1{1+\rho^2},\quad
\int R_\rho=1.
\]

所以

\[
\int(S_\rho-1)^2=\frac{\rho^4}{1-\rho^4}.
\]

同一正交不变性给出||A||₂=||f||₂||g||₂。Cauchy–Schwarz因此得到

\[
|E[f(X)g(Y)]|\le
\frac{\rho^2}{\sqrt{1-\rho^4}}\|f\|_2\|g\|_2.
\]

当|rho|≤1/2，这小于等于4rho²||f||₂||g||₂。当|rho|>1/2，直接对原联合分布使用Cauchy–Schwarz，得到||f||₂||g||₂≤4rho²||f||₂||g||₂；这也覆盖rho=±1。

证明不需要Hermite展开或完备性。常数4无需最优；足以把相关平方求和转为对数统计量方差界。
