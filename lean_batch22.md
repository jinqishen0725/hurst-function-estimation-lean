# 第二十二阶段：q=1未知尺度全域风险与minimax

新增46条数学定理，累计865条数学定理及3条编号检查。主线未完成；原27个编号结果仍为2项完整。

范围是原Hölder类p≥1、固定0<a≤H≤b<3/4和任意未知共同σ≠0。包含p=1。每个固定正整数步长均从真实谱特征证明全域协方差扰动、非退化、相关平方行和和精细对数均值。两个pilot尺度使用原n个观测中的n−2个共同基点，保留真实相关。

`FirstPilotRisk`证明实际未知尺度pilot的MSE。`FirstScaleBias`证明采用同一合并权重时H主项逐点精确消去，无非线性修正；线性尺度方差为O(log²n/n)。`FirstScaleSharperRisk`得到尺度MSE/log²n≤C/n，`FirstScaleUnknownRisk`将最优速率界传递至任意未知σ。

`FirstUnknownEstimator`和`FirstUnknownDecision`验证最终回代估计器的联合可测性、空间连续性及Ls决策可测性。`FirstUnknownInvariance`证明实际尺度不变性。`FirstUnknownLpRisk`给出全(0,1)上1≤s≤2的平方Ls风险≤C(n log²n)^(-2p/(2p+1))。

`unknownScale_q1_minimax_matched`把同一个不依赖σ的决策核与固定σ子模型的下界接合。匹配范围要求0<a<1/2<b<3/4、M>0；下界对任意随机化可测估计器成立。上界单独不要求值域跨越1/2。

实现采用全域粗平均，具体直接证明见[说明](proof_notes/q1_unknown_scale.md)。至此q=1短记忆及q=2在1≤s≤2内的已知/未知尺度风险与minimax链均闭合。s>2、高阶矩、精细偏差和短/临界/长记忆极限仍在主线，未移入backlog、未改标完成。
