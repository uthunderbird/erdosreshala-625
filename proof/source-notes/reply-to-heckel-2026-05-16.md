# Reply to Dr. Heckel — 2026-05-16

## Subject: Re: Lean formalization of a result related to your work on Erdős Problem 625

Dear Dr. Heckel,

Thank you for your quick response, and please enjoy your holiday — there is no rush. I wanted to write up the argument carefully before asking, so that the question is as precise as I can make it.

The specific thing I am hoping you might be able to clarify is whether the applicability conditions of your Co. 39 hold for (alpha-2)-bounded profiles at threshold k_{alpha-1} in the crossing regime, and, if so, whether the second-moment ratio E[X^2]/E[X]^2 remains O(1) in that setting. Let me explain the structure of the argument, and then be honest about exactly where I am stuck.

The cochromatic upper bound I am aiming for is P[ zeta(G(n,1/2)) <= k_{alpha-1} + n^{0.99} ] >= 1 - epsilon. The choice of k_{alpha-1} as the target — rather than k_{alpha-2} — is dictated by what the gap argument needs: combining chi >= k_{alpha-2} - n^{0.99} with zeta <= k_{alpha-1} + n^{0.99} gives a gap of k_{alpha-2} - k_{alpha-1} - 2·n^{0.99}, which is at least n^{1-epsilon} by the threshold-gap lemma. Targeting k_{alpha-2} as the cochromatic upper bound would give a trivially small gap.

The reason for working with (alpha-2)-bounded profiles is that I need the expected count of cocolourings to be large enough for Paley–Zygmund to apply. At k_{alpha-1} in the crossing regime, the (alpha-1)-bounded count is too small for Co. 39's hypothesis to be satisfied, whereas mu_{alpha-2} at this threshold is of order n^2/log^2(n) · mu_alpha, which I expect to satisfy the lower-bound hypothesis. The profile-index shift from {1,...,alpha-1} to {1,...,alpha-2} also keeps the entropy and overlap decompositions in the second-moment argument uniform in a = alpha + O(1).

Where I am genuinely stuck is in verifying that these expectations are correct. I have not established that Co. 39's applicability conditions hold at threshold k_{alpha-1} with (alpha-2)-bounded profiles in the crossing regime — specifically, that mu_{alpha-2} at this threshold satisfies the lower-bound hypothesis. And even if they do, I have not controlled the second-moment ratio E[X^2]/E[X]^2 = O(1) for this regime, which is needed for Paley–Zygmund to yield P[X > 0] bounded away from zero. Both conditions are asserted without proof in my current draft, and I do not know a clean way to derive them from what is written in the paper.

If you are able to say briefly whether these conditions are likely to follow from the structure of your Prop 5(b) argument, or point me to the relevant part of the paper, that would be enormously helpful.

With thanks,
Daniyar Supiyev
