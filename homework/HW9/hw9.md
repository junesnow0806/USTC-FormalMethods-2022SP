# 形式化方法导引-作业9

***

梁峻滔 PB19051175

***

[toc]

## EX1

### 代码

```Coq
Lemma ex1: forall A : Prop,
~~~A -> ~A.
Proof.
intro A.
intro H1.
contradict H1.
intro H2.
contradict H2.
assumption.
Qed.
```

### 证明过程

![image-20220524204023552](D:\USTC\FM2022\homework\HW9\hw9.assets\image-20220524204023552.png)

![image-20220524204034932](D:\USTC\FM2022\homework\HW9\hw9.assets\image-20220524204034932.png)

![image-20220524204052869](D:\USTC\FM2022\homework\HW9\hw9.assets\image-20220524204052869.png)

>根据[官方文档的描述]([Tactics — Coq 8.15.1 documentation (inria.fr)](https://coq.inria.fr/distrib/current/refman/proof-engine/tactics.html#classical-tactics)), 当执行`contradict H`后, "the current goal and context is transformed in the following way:"
>
>* H:¬A ⊢ B becomes ⊢ A
>
>* H:¬A ⊢ ¬B becomes H: B ⊢ A
>* H: A ⊢ B becomes ⊢ ¬A
>* H: A ⊢ ¬B becomes H: B ⊢ ¬A
>
>下面执行`contradict H1`后对应第二种情况.

![image-20220524204108164](D:\USTC\FM2022\homework\HW9\hw9.assets\image-20220524204108164.png)

>根据PPT [6.2.1-2]([6.2.1-2 (ustc.edu.cn)](http://staff.ustc.edu.cn/~huangwc/fm/6.2.1-2.pdf)) 中18页处所给的tactics列表中的这一项
>
>![image-20220524205846451](D:\USTC\FM2022\homework\HW9\hw9.assets\image-20220524205846451.png)
>
>此处执行`intro H2`后会将原来的goal去掉一个否定词后作为新的hypothesis, 然后goal变成False.

![image-20220524204117934](D:\USTC\FM2022\homework\HW9\hw9.assets\image-20220524204117934.png)

>再应用一次`contradict`就可以把goal变成True -> A, 即A.
>
>然后刚好我们的假设里有H1 : A.

![image-20220524204128125](D:\USTC\FM2022\homework\HW9\hw9.assets\image-20220524204128125.png)

![image-20220524204137991](D:\USTC\FM2022\homework\HW9\hw9.assets\image-20220524204137991.png)

## EX2

### 代码

```Coq
Lemma ex2 : forall A B : Prop,
A \/ B -> ~(~A /\ ~B).
Proof.
intros A B.
intro H1.
intro H2.
destruct H1 as [H3|H4].
destruct H2 as [H5 H6].
contradict H5.
assumption.
destruct H2 as [H5 H6].
contradict H6.
assumption.
Qed.
```

### 证明过程

![image-20220524204335484](D:\USTC\FM2022\homework\HW9\hw9.assets\image-20220524204335484.png)

![image-20220524204346058](D:\USTC\FM2022\homework\HW9\hw9.assets\image-20220524204346058.png)

![image-20220524204401749](D:\USTC\FM2022\homework\HW9\hw9.assets\image-20220524204401749.png)

![image-20220524204411459](D:\USTC\FM2022\homework\HW9\hw9.assets\image-20220524204411459.png)

>这里对是析取式的假设H1执行`destruct`就是分情况讨论: A成立或B成立.
>
>H3对应A成立的分支, 该分支需要证明goal1. 后面还需要在B成立的第二个分支证明goal2(这里 goal1 和 goal2 都是False).

![image-20220524204420197](D:\USTC\FM2022\homework\HW9\hw9.assets\image-20220524204420197.png)

>看到假设中有合取式, 我们可以考虑将其拆分成两个假设, 也是使用`destruct`.
>
>将H2分成了H5和H6.

![image-20220524204428826](D:\USTC\FM2022\homework\HW9\hw9.assets\image-20220524204428826.png)

>在A成立的假设分支中, 对 H5(¬A) 和 goal1(False) 应用`contradict`就能把 goal 变成 A.
>
>而刚好 H3 就是A.

![image-20220524204440595](D:\USTC\FM2022\homework\HW9\hw9.assets\image-20220524204440595.png)

![image-20220524204449239](D:\USTC\FM2022\homework\HW9\hw9.assets\image-20220524204449239.png)

>下面重复类似的操作来证明第二个分支.

![image-20220524204502912](D:\USTC\FM2022\homework\HW9\hw9.assets\image-20220524204502912.png)

![image-20220524204514900](D:\USTC\FM2022\homework\HW9\hw9.assets\image-20220524204514900.png)

![image-20220524204535238](D:\USTC\FM2022\homework\HW9\hw9.assets\image-20220524204535238.png)

## EX3

### Heurisitics

PPT [6.2.1-2]([6.2.1-2 (ustc.edu.cn)](http://staff.ustc.edu.cn/~huangwc/fm/6.2.1-2.pdf)) 18页的表和以下这张表:

![image-20220524211805802](D:\USTC\FM2022\homework\HW9\hw9.assets\image-20220524211805802.png)

来源: [Coq in a Hurry]([Coq in a Hurry (archives-ouvertes.fr)](https://cel.archives-ouvertes.fr/inria-00001173v6/document)). 这两张表的参考方式是: 例如, 看到某个假设 H 中含有否定词, 则考虑对 H 使用`elim`; 要证明的 goal 的命题中最前面是exists, 则考虑使用`exists`.

### 代码

```Coq
Lemma ex3: forall T (P:T -> Prop),
(~exists x, P x) -> forall x, ~ P x.
Proof.
intro T.
intro P.
intro H1.
intro x.
intro H2.
elim H1.
exists x.
exact H2.
Qed.
```

### 证明过程

![image-20220524204627497](D:\USTC\FM2022\homework\HW9\hw9.assets\image-20220524204627497.png)

![image-20220524204636994](D:\USTC\FM2022\homework\HW9\hw9.assets\image-20220524204636994.png)

![image-20220524204644110](D:\USTC\FM2022\homework\HW9\hw9.assets\image-20220524204644110.png)

![image-20220524204651844](D:\USTC\FM2022\homework\HW9\hw9.assets\image-20220524204651844.png)

![image-20220524204659264](D:\USTC\FM2022\homework\HW9\hw9.assets\image-20220524204659264.png)

>goal中含forall, 考虑intro.

![image-20220524204710149](D:\USTC\FM2022\homework\HW9\hw9.assets\image-20220524204710149.png)

![image-20220524204718257](D:\USTC\FM2022\homework\HW9\hw9.assets\image-20220524204718257.png)

>考察假设, 发现 H1 比较复杂, 然后最前面是否定词, 考虑使用`elim`.

![image-20220524204727058](D:\USTC\FM2022\homework\HW9\hw9.assets\image-20220524204727058.png)

>goal是 exists 命题, 考虑使用`exists` tactic.
>
>Oops! 刚好目标就是H2.

![image-20220524204734743](D:\USTC\FM2022\homework\HW9\hw9.assets\image-20220524204734743.png)

![image-20220524204743106](D:\USTC\FM2022\homework\HW9\hw9.assets\image-20220524204743106.png)





