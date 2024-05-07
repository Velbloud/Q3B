#include "UnconstrainedVariableSimplifier.h"
#include <fstream>
#include <sstream>
#include <cmath>
#include "ExprSimplifier.h"
#include <algorithm>
#include <sstream>
#include <boost/integer/mod_inverse.hpp>
#include <gmp.h>

using namespace std;
using namespace z3;
using boost::integer::mod_inverse;


map<string, int> UnconstrainedVariableSimplifier::countVariableOccurences(expr e, bool isPositive, Goal goal = NONE)
{
    if (e.get_sort().is_bv())
    {
        auto item = subformulaVariableCounts.find({e, isPositive, goal});
        if (item != subformulaVariableCounts.end())
        {
            cacheHits++;
            if (dagCounting)
            {
                map<string, int> varCounts;
                return varCounts;
            }
            else
            {
                return (item->second);
            }
        }
    }

    map<string, int> varCounts;
    if (e.is_const() && !e.is_numeral())
    {
	if (e.get_sort().is_bool())
	{
	    if (e.decl().decl_kind() == Z3_OP_TRUE || e.decl().decl_kind() == Z3_OP_FALSE)
	    {
		return varCounts;
	    }

	    varCounts[e.decl().name().str()] = 1;
	}
	else if (e.get_sort().is_bv())
	{
	    varCounts[e.decl().name().str()] = 1;
	}

	return varCounts;
    }
    else if (e.is_app())
    {
	func_decl f = e.decl();
	unsigned num = e.num_args();

	if (num != 0)
	{
	    auto decl_kind = e.decl().decl_kind();

	    if (decl_kind == Z3_OP_NOT)
	    {
		return countVariableOccurences(e.arg(0), !isPositive);
	    }
	    else if (decl_kind == Z3_OP_IFF || (decl_kind == Z3_OP_EQ && e.arg(0).is_bool()))
	    {
		addCounts(countVariableOccurences(e.arg(0), isPositive), varCounts);
		addCounts(countVariableOccurences(e.arg(1), isPositive), varCounts);

		return varCounts;
	    }
	    else if (decl_kind == Z3_OP_IMPLIES)
	    {
		addCounts(countVariableOccurences(e.arg(0), !isPositive), varCounts);
		addCounts(countVariableOccurences(e.arg(1), isPositive), varCounts);

		return varCounts;
	    }
	    else if (decl_kind == Z3_OP_ITE)
	    {
		//counts(ite(a, b, c)) = 2*counts(a) + max(counts(b), counts(c))
                varCounts = countVariableOccurences(e.arg(1), isPositive);
		maxCounts(countVariableOccurences(e.arg(2), isPositive), varCounts);

                auto origDagCounting = dagCounting;
                dagCounting = false;
                auto condCounts = countVariableOccurences(e.arg(0), isPositive);
		addCounts(condCounts, varCounts);
                addCounts(condCounts, varCounts);
                dagCounting = origDagCounting;

		return varCounts;
	    }

            if (decl_kind == Z3_OP_ULEQ || decl_kind == Z3_OP_ULT)
            {
                addCounts(countVariableOccurences(e.arg(0), isPositive, UNSIGN_MIN), varCounts);
                addCounts(countVariableOccurences(e.arg(1), isPositive, UNSIGN_MAX), varCounts);
                return varCounts;
            }

            if (decl_kind == Z3_OP_UGEQ || decl_kind == Z3_OP_UGT)
            {
                addCounts(countVariableOccurences(e.arg(0), isPositive, UNSIGN_MAX), varCounts);
                addCounts(countVariableOccurences(e.arg(1), isPositive, UNSIGN_MIN), varCounts);
                return varCounts;
            }

            if (decl_kind == Z3_OP_SLEQ || decl_kind == Z3_OP_SLT)
            {
                addCounts(countVariableOccurences(e.arg(0), isPositive, SIGN_MIN), varCounts);
                addCounts(countVariableOccurences(e.arg(1), isPositive, SIGN_MAX), varCounts);
                return varCounts;
            }

            if (decl_kind == Z3_OP_SGEQ || decl_kind == Z3_OP_SGT)
            {
                addCounts(countVariableOccurences(e.arg(0), isPositive, SIGN_MAX), varCounts);
                addCounts(countVariableOccurences(e.arg(1), isPositive, SIGN_MIN), varCounts);
                return varCounts;
            }

            for (unsigned i = 0; i < num; i++)
            {
                addCounts(countVariableOccurences(e.arg(i), isPositive), varCounts);
            }
	}
	else if (f.name() != NULL)
	{
	    z3::sort s = f.range();

	    if ((s.is_bv() && !e.is_numeral()) || (s.is_bool() && !e.is_const()))
	    {
		stringstream ss;
		ss << e;
		varCounts[ss.str()] = 1;
	    }
	}

        if (e.get_sort().is_bv() && !e.is_numeral())
        {
            subformulaVariableCounts.insert({{e, isPositive, goal}, varCounts});
            subformulaVariableCounts.insert({{e, !isPositive, goal}, varCounts});
        }
	return varCounts;
    }
    else if(e.is_quantifier())
    {
	Z3_ast ast = (Z3_ast)e;
	int numBound = Z3_get_quantifier_num_bound(*context, ast);

        z3::expr_vector boundVars(*context);

	for (int i = numBound - 1; i >= 0; i--)
	{
	    Z3_symbol z3_symbol = Z3_get_quantifier_bound_name(*context, ast, i);
            Z3_sort z3_sort = Z3_get_quantifier_bound_sort(*context, ast, i);
	    symbol current_symbol(*context, z3_symbol);
            z3::sort current_sort(*context, z3_sort);

            if (current_sort.is_bool())
            {
                boundVars.push_back(context->bool_const(current_symbol.str().c_str()));
            }
            else //is BV
            {
                boundVars.push_back(context->bv_const(current_symbol.str().c_str(), current_sort.bv_size()));
            }
	}

	auto result = countVariableOccurences(e.body().substitute(boundVars).simplify(), isPositive);

	return result;
    }

    std::cout << e << std::endl;
    assert(false);
    return varCounts;
}

void UnconstrainedVariableSimplifier::SimplifyIte()
{
    std::vector<BoundVar> boundVars;
    variableCounts = countFormulaVarOccurences(expression);

    bool anyUnconstrained = std::any_of(variableCounts.begin(), variableCounts.end(), [](const auto& var) { return var.second == 1; });
    if (!anyUnconstrained)
    {
	return;
    }

    unsigned oldHash = 0;

    while (oldHash != expression.hash())
    {
	oldHash = expression.hash();

	SimplifyOnce();
	expression = expression.simplify();

	subformulaVariableCounts.clear();
	std::vector<BoundVar> boundVars;
	variableCounts = countFormulaVarOccurences(expression);

	trueSimplificationCache.clear();
	falseSimplificationCache.clear();
    }
}

z3::expr UnconstrainedVariableSimplifier::simplifyOnce(expr e, std::vector<BoundVar> boundVars, bool isPositive = true, Goal goal = NONE)
{
    if (e.is_var() || e.is_numeral())
    {
	return e;
    }

    if (forcedGoal.has_value())
    {
        goal = forcedGoal.value();
    }

    cacheMapType::iterator item;

    if (isPositive)
    {
	item = trueSimplificationCache.find(e);
    }
    else
    {
	item = falseSimplificationCache.find(e);
    }

    if (((isPositive && item != trueSimplificationCache.end()) || (!isPositive && item != falseSimplificationCache.end())))
    {
	auto cachedBoundVars =  (item->second).second;
	bool correctBoundVars = true;

	int pairsCount = min(boundVars.size(), cachedBoundVars.size());

	for (int i = 0; i < pairsCount; i++)
	{
	    string oldVarName = std::get<0>(cachedBoundVars[cachedBoundVars.size() - i - 1]);
	    string newVarName = std::get<0>(boundVars[boundVars.size() - i - 1]);

	    if (oldVarName != newVarName)
	    {
		correctBoundVars = false;
	    }
	}

	if (correctBoundVars)
	{
	    return (item->second).first;
	}
    }

    if (e.is_app())
    {
	func_decl f = e.decl();
	unsigned num = e.num_args();
	auto decl_kind = f.decl_kind();

    if (decl_kind == Z3_OP_BADD || decl_kind == Z3_OP_BXOR)
	{
        for (unsigned int i = 0; i < num; i++)
        {
            if (!isUnconstrained(e.arg(i), boundVars))
            {
                continue;
            }

            bool allBefore = true;
            for (unsigned int j = 0; j < num; j++)
            {
                if (i != j && !isBefore(e.arg(j), e.arg(i), boundVars, isPositive))
                {
                    allBefore = false;
                    break;
                }
            }

            if (allBefore)
            {
                long int bvSize = e.arg(0).get_sort().bv_size();
                expr e_without_unconstr_vars = context->bv_val(0, bvSize);
                if (decl_kind == Z3_OP_BADD) {
                    if (isFreeVariable(e.arg(i))) {
                        for (unsigned int j = 0; j < num; j++) {
                            if (i != j) {
                                e_without_unconstr_vars = to_expr(*context, Z3_mk_bvadd(*context, (Z3_ast) e_without_unconstr_vars, (Z3_ast)e.arg(j)));
                            }
                        }
                        appliedSubstitutions.push_back({e.arg(i), to_expr(*context, e.arg(i) - e_without_unconstr_vars), false});
                    }
                }
                else {
                    if (isFreeVariable(e.arg(i))) {
                        for (unsigned int j = 0; j < num; j++) {
                            if (i != j) {
                                e_without_unconstr_vars = to_expr(*context, Z3_mk_bvxor(*context, (Z3_ast) e_without_unconstr_vars, (Z3_ast)e.arg(j)));
                            }
                        }
                        appliedSubstitutions.push_back({e.arg(i), to_expr(*context, e.arg(i) - e_without_unconstr_vars), false});
                    }
                }
                return e.arg(i);
            }
        }
	}
	else if (decl_kind == Z3_OP_BNOT)
	{
	    if (isUnconstrained(e.arg(0), boundVars))
	    {
            if(isFreeVariable(e.arg(0)))
                appliedSubstitutions.push_back({e.arg(0), e, false});
            return e.arg(0);
	    }
	}
	else if (decl_kind == Z3_OP_BAND || decl_kind == Z3_OP_BOR)
	{
	    bool unconstrained0 = isUnconstrained(e.arg(0), boundVars);
	    bool unconstrained1 = isUnconstrained(e.arg(1), boundVars);

	    if (unconstrained0 && unconstrained1 &&
                getBoundType(e.arg(0), boundVars) == getBoundType(e.arg(1), boundVars))
	    {

        int bvSize = e.arg(1).get_sort().bv_size();
        expr zero = context->bv_val(0, bvSize);
        expr ones = context->bv_val(-1, bvSize);

		if (isBefore(e.arg(0), e.arg(1), boundVars, isPositive))
		{
            if (decl_kind == Z3_OP_BAND) {
                if(isFreeVariable(e.arg(0)))
                    appliedSubstitutions.push_back({e.arg(0), ones, false});
            }
            if (decl_kind == Z3_OP_BOR) {
                if(isFreeVariable(e.arg(0)))
                    appliedSubstitutions.push_back({e.arg(0), zero, false});
            }
            return e.arg(1);
		}
		else
		{
            if (decl_kind == Z3_OP_BAND) {
                if(isFreeVariable(e.arg(1)))
                    appliedSubstitutions.push_back({e.arg(1), ones, false});
            }
            if (decl_kind == Z3_OP_OR) {
                if(isFreeVariable(e.arg(1)))
                    appliedSubstitutions.push_back({e.arg(1), zero, false});
            }
		    return e.arg(0);
		}
	    }
	}
    else if (decl_kind == Z3_OP_BMUL && num == 2)
	{
	    bool unconstrained0 = isUnconstrained(e.arg(0), boundVars);
	    bool unconstrained1 = isUnconstrained(e.arg(1), boundVars);

        int bvSize = e.arg(0).get_sort().bv_size();
        expr one = context->bv_val(1, bvSize);
        expr ones = context->bv_val(-1, bvSize);
        expr zero = context->bv_val(0, bvSize);
        auto maxSigned = concat(context->bv_val(0, 1), context->bv_val(-1, bvSize - 1)); //011...1


        if (unconstrained0 && unconstrained1 &&
                getBoundType(e.arg(0), boundVars) == getBoundType(e.arg(1), boundVars))
	    {
		if (isBefore(e.arg(0), e.arg(1), boundVars, isPositive))
		{
            if (isFreeVariable(e.arg(1)))
                appliedSubstitutions.push_back({e.arg(0), one, false});
		    return e.arg(1);
		}
		else
		{
            if (isFreeVariable(e.arg(0)))
                appliedSubstitutions.push_back({e.arg(1), one, false});
		    return e.arg(0);
		}
	    }
	    else if (unconstrained0 && isBefore(e.arg(1), e.arg(0), boundVars, isPositive))
	    {
            if (goalUnconstrained) {
                bool flip = (!isPositive && getBoundType(e.arg(0), boundVars) == EXISTENTIAL) ||
                            (isPositive && getBoundType(e.arg(0), boundVars) == UNIVERSAL);

                if ((!flip && goal == SIGN_MAX) || (flip && goal == SIGN_MIN)) {
                    if (isFreeVariable(e.arg(0))) {
                        appliedSubstitutions.push_back({e.arg(0), maxSigned, false});
                        appliedSubstitutions.push_back({e.arg(0), e.arg(1), true});
                    }
                    return maxSigned & (e.arg(1) | -e.arg(1));
                } else if ((!flip && goal == UNSIGN_MAX) || (flip && goal == UNSIGN_MIN)) {
                    if (isFreeVariable(e.arg(0))) {
                        appliedSubstitutions.push_back({e.arg(0), ones, false});
                        appliedSubstitutions.push_back({e.arg(0), e.arg(1), true});
                    }
                    return (e.arg(1) | -e.arg(1));
                } else if ((!flip && goal == SIGN_MIN) || (flip && goal == SIGN_MAX)) {
                    auto minSigned = z3::concat(context->bv_val(1, 1), context->bv_val(0, bvSize - 1)); //1000...0
                    if (isFreeVariable(e.arg(0))) {
                        appliedSubstitutions.push_back({e.arg(0), minSigned, false});
                        appliedSubstitutions.push_back({e.arg(0), e, true});
                    }
                    return z3::ite(e.arg(1) == zero, zero,minSigned);
                } else if ((!flip && goal == UNSIGN_MIN) || (flip && goal == UNSIGN_MAX)) {
                    if (isFreeVariable(e.arg(0))) {
                        appliedSubstitutions.push_back({e.arg(0), zero, false});
                    }
                    return zero;
                }
            }

            if (isFreeVariable(e.arg(0))) {
                appliedSubstitutions.push_back({e.arg(0), e, true});
            }
            return e.arg(0) & (e.arg(1) | -e.arg(1));
	    }


	    else if (unconstrained1 && isBefore(e.arg(0), e.arg(1), boundVars, isPositive))
	    {
            if (isFreeVariable(e.arg(1))) {
                appliedSubstitutions.push_back({e.arg(1), e.arg(0), true});
            }
            return e.arg(1) & (e.arg(0) | -e.arg(0));
	    }
	}
	else if (decl_kind == Z3_OP_BSHL)
	{
	    bool unconstrained0 = isUnconstrained(e.arg(0), boundVars);
	    bool unconstrained1 = isUnconstrained(e.arg(1), boundVars);

        int bvSize = e.arg(1).get_sort().bv_size();
        expr zero = context->bv_val(0, bvSize);
        expr one = context->bv_val(1, bvSize);
        expr zeroes = context->bv_val(0, bvSize);
        expr ones = context->bv_val(-1, bvSize);

	    if (unconstrained0 && unconstrained1 &&
                getBoundType(e.arg(0), boundVars) == getBoundType(e.arg(1), boundVars))
	    {
		if (isBefore(e.arg(0), e.arg(1), boundVars, isPositive))
		{
            if (isFreeVariable(e.arg(0)) && isFreeVariable(e.arg(1))) {
                appliedSubstitutions.push_back({e.arg(1), zero, false});
                appliedSubstitutions.push_back({e.arg(0), e.arg(1), false});
            }
		    return e.arg(1);
		}
		else
		{
            if (isFreeVariable(e.arg(1)))
                appliedSubstitutions.push_back({e.arg(1), zero, false});
		    return e.arg(0);
		}
	    }
	    else if (unconstrained0 && isBefore(e.arg(1), e.arg(0), boundVars, isPositive))
	    {
            expr arg1 = e.arg(1);

            if (goalUnconstrained)
                {
                    bool flip = (!isPositive && getBoundType(e.arg(0), boundVars) == EXISTENTIAL) ||
                        (isPositive && getBoundType(e.arg(0), boundVars) == UNIVERSAL);

                    if ((!flip && goal == SIGN_MAX) || (flip && goal == SIGN_MIN))
                    {
                        auto maxSigned = concat(context->bv_val(0, 1), context->bv_val(-1, bvSize - 1)); //011...1
                        if (isFreeVariable(e.arg(0))) {
                            appliedSubstitutions.push_back({e.arg(0), z3::ashr(maxSigned, arg1), false});
                        }
                        return z3::shl(z3::ashr(maxSigned, arg1), arg1);
                    }
                    else if ((!flip && goal == UNSIGN_MAX) || (flip && goal == UNSIGN_MIN))
                    {
                        if (isFreeVariable(e.arg(0))) {
                            appliedSubstitutions.push_back({e.arg(0), ones, false});
                        }
                        return z3::shl(ones, e.arg(1));
                    }
                    else if ((!flip && goal == SIGN_MIN) || (flip && goal == SIGN_MAX))
                    {
                        auto minSigned = z3::concat(context->bv_val(1, 1), context->bv_val(0, bvSize - 1)); //1000...0
                        if (isFreeVariable(e.arg(0))) {
                            appliedSubstitutions.push_back({e.arg(0), z3::ashr(minSigned, arg1), false});
                        }
                        return z3::ite(z3::ult(arg1, bvSize), minSigned, zeroes);
                    }
                    else if ((!flip && goal == UNSIGN_MIN) || (flip && goal == UNSIGN_MAX))
                    {
                        if (isFreeVariable(e.arg(0))) {
                            appliedSubstitutions.push_back({e.arg(0), zero, false});
                        }
                        return zeroes;
                    }
                }

		    auto shiftExpr = to_expr(*context, Z3_mk_bvshl(*context, (Z3_ast)ones, (Z3_ast)arg1));

            if (isFreeVariable(e.arg(0))) {
                expr subst = to_expr(*context, Z3_mk_bvlshr(*context, (Z3_ast)e.arg(0), (Z3_ast)e.arg(1)));
                appliedSubstitutions.push_back({e.arg(0), subst, false});
            }
            return (e.arg(0) & shiftExpr);
	    }
	    else if (unconstrained1 && isBefore(e.arg(0), e.arg(1), boundVars, isPositive))
	    {
            if (goalUnconstrained)
            {
                bool flip = (!isPositive && getBoundType(e.arg(1), boundVars) == EXISTENTIAL) ||
                        (isPositive && getBoundType(e.arg(1), boundVars) == UNIVERSAL);

                if ((!flip && goal == UNSIGN_MIN) || (flip && goal == UNSIGN_MAX))
                {
                    if (isFreeVariable(e.arg(1))) {
                        appliedSubstitutions.push_back({e.arg(1), ones, false}); // nerozumim nevyhodnosti
                    }
                    return zeroes;
                }
                else if ((!flip && goal == SIGN_MIN) || (flip && goal == SIGN_MAX))
                {
                    auto minSigned = z3::concat(context->bv_val(1, 1), context->bv_val(0, bvSize - 1)); //1000...0
                    //je to problematičtější, je potřeba najít kde je v arg1 jednička
                    return z3::ite(e.arg(0) == 0, zeroes, minSigned);
                }
            }
	    }
	}
	else if (decl_kind == Z3_OP_BLSHR)
	{
	    bool unconstrained0 = isUnconstrained(e.arg(0), boundVars);
	    bool unconstrained1 = isUnconstrained(e.arg(1), boundVars);

        int bvSize = e.arg(1).get_sort().bv_size();
        expr zero = context->bv_val(0, bvSize);
        expr one = context->bv_val(1, bvSize);
        expr ones = context->bv_val(-1, bvSize);
        expr zeroes = context->bv_val(0, bvSize);

	    if (unconstrained0 && unconstrained1 &&
            getBoundType(e.arg(0), boundVars) == getBoundType(e.arg(1), boundVars))
	    {
		    if (isBefore(e.arg(0), e.arg(1), boundVars, isPositive))
		    {
                if(isFreeVariable(e.arg(0)) && isFreeVariable(e.arg(1))) {
                    appliedSubstitutions.push_back({e.arg(1), zero, false});
                    appliedSubstitutions.push_back({e.arg(0), e.arg(1), false});
                }
                return e.arg(1);
		    }
		    else
		    {
                if(isFreeVariable(e.arg(0)) && isFreeVariable(e.arg(1)))
                    appliedSubstitutions.push_back({e.arg(1), zero, false});
		        return e.arg(0);
		    }
	    }
	    else if (unconstrained0 && isBefore(e.arg(1), e.arg(0), boundVars, isPositive))
	    {
		    expr arg1 = e.arg(1);

            if (goalUnconstrained)
            {
                bool flip = (!isPositive && getBoundType(e.arg(0), boundVars) == EXISTENTIAL) ||
                        (isPositive && getBoundType(e.arg(0), boundVars) == UNIVERSAL);

                if ((!flip && goal == SIGN_MAX) || (flip && goal == SIGN_MIN))
                {
                    auto maxSigned = concat(context->bv_val(0, 1), context->bv_val(-1, bvSize - 1));
                    if (isFreeVariable(e.arg(0))) {
                        appliedSubstitutions.push_back({e.arg(0), z3::ite(arg1 == 0, maxSigned, ones), false});
                    }
                    return z3::ite(arg1 == 0, maxSigned, to_expr(*context, Z3_mk_bvlshr(*context, ones, arg1)));
                }
                else if ((!flip && goal == UNSIGN_MAX) || (flip && goal == UNSIGN_MIN))
                {
                    if (isFreeVariable(e.arg(0))) {
                        appliedSubstitutions.push_back({e.arg(0), ones, false});
                    }
                    return to_expr(*context, Z3_mk_bvlshr(*context, ones, arg1));
                }
                else if ((!flip && goal == SIGN_MIN) || (flip && goal == SIGN_MAX))
                {
                    auto minSigned = z3::concat(context->bv_val(1, 1), context->bv_val(0, bvSize - 1)); //1000...0
                    if (isFreeVariable(e.arg(0))) {
                        appliedSubstitutions.push_back({e.arg(0), ones, false});
                    }
                    return z3::ite(arg1 == 0, minSigned, zeroes);
                }
                else if ((!flip && goal == UNSIGN_MIN) || (flip && goal == UNSIGN_MAX))
                {
                    if (isFreeVariable(e.arg(0))) {
                        appliedSubstitutions.push_back({e.arg(0), zero, false});
                    }
                    return zeroes;
                }
            }

		    auto shiftExpr = to_expr(*context, Z3_mk_bvlshr(*context, (Z3_ast)ones, (Z3_ast)arg1));

            if(isFreeVariable(e.arg(0))) {
                expr subst = to_expr(*context, Z3_mk_bvlshr(*context, (Z3_ast)e.arg(0), (Z3_ast)arg1));
                appliedSubstitutions.push_back({e.arg(0), subst, false});
            }
            return (e.arg(0) & shiftExpr);
	    }
        else if (unconstrained1 && isBefore(e.arg(0), e.arg(1), boundVars, isPositive))
	    {
		    expr arg0 = e.arg(0);

            if (goalUnconstrained)
            {
                bool flip = (!isPositive && getBoundType(e.arg(1), boundVars) == EXISTENTIAL) ||
                    (isPositive && getBoundType(e.arg(1), boundVars) == UNIVERSAL);

                if ((!flip && goal == SIGN_MAX) || (flip && goal == SIGN_MIN))
                {
                    if (isFreeVariable(e.arg(1))) {
                        appliedSubstitutions.push_back({e.arg(1), z3::ite(arg0.extract(bvSize-1, bvSize-1) == 0, zero, one), false});
                    }
                    return z3::ite(arg0.extract(bvSize-1, bvSize-1) == 0, arg0, f(arg0, 1));
                }
                else if ((!flip && goal == UNSIGN_MAX) || (flip && goal == UNSIGN_MIN))
                {
                    if (isFreeVariable(e.arg(1))) {
                        appliedSubstitutions.push_back({e.arg(1), zero, false});
                    }
                    return arg0;
                }
                else if ((!flip && goal == SIGN_MIN) || (flip && goal == SIGN_MAX))
                {
                    if (isFreeVariable(e.arg(1))) {
                        appliedSubstitutions.push_back({e.arg(1), z3::ite(arg0.extract(bvSize-1, bvSize-1) == 0, ones, zero), false});
                    }
                    return z3::ite(arg0.extract(bvSize-1, bvSize-1) == 0, zeroes, arg0);
                }
                else if ((!flip && goal == UNSIGN_MIN) || (flip && goal == UNSIGN_MAX))
                {
                    if (isFreeVariable(e.arg(1))) {
                        appliedSubstitutions.push_back({e.arg(1), ones, false});
                    }
                    return zeroes;
                }
            }
	    }
	}
	else if (decl_kind == Z3_OP_BASHR)
	{
	    bool unconstrained0 = isUnconstrained(e.arg(0), boundVars);
	    bool unconstrained1 = isUnconstrained(e.arg(1), boundVars);

        int bvSize = e.arg(1).get_sort().bv_size();
        expr zero = context->bv_val(0, bvSize);
        expr one = context->bv_val(1, bvSize);

	    if (unconstrained0 && unconstrained1 &&
                getBoundType(e.arg(0), boundVars) == getBoundType(e.arg(1), boundVars))
	    {
            if (isBefore(e.arg(0), e.arg(1), boundVars, isPositive))
            {
                if(isFreeVariable(e.arg(0)) && isFreeVariable(e.arg(1))) {
                    appliedSubstitutions.push_back({e.arg(1), zero, false});
                    appliedSubstitutions.push_back({e.arg(0), e.arg(1), false});
                }
                return e.arg(1);
            }
            else
            {
                if(isFreeVariable(e.arg(0)) && isFreeVariable(e.arg(1)))
                    appliedSubstitutions.push_back({e.arg(1), zero, false});
                return e.arg(0);
            }
	    }
	    else if (unconstrained0 && isBefore(e.arg(1), e.arg(0), boundVars, isPositive))
	    {
            int bvSize = e.arg(1).get_sort().bv_size();
		    expr arg1 = e.arg(1);
            expr ones = context->bv_val(-1, bvSize);
            expr zeroes = context->bv_val(0, bvSize);
            auto minSigned = z3::concat(context->bv_val(1, 1), context->bv_val(0, bvSize - 1)); //1000...0
            if (goalUnconstrained)
            {
                bool flip = (!isPositive && getBoundType(e.arg(0), boundVars) == EXISTENTIAL) || (isPositive && getBoundType(e.arg(0), boundVars) == UNIVERSAL);

                if ((!flip && goal == SIGN_MAX) || (flip && goal == SIGN_MIN))
                {
                    auto maxSigned = concat(context->bv_val(0, 1), context->bv_val(-1, bvSize - 1));
                    if (isFreeVariable(e.arg(0))) {
                        appliedSubstitutions.push_back({e.arg(0), maxSigned, false});
                    }
                    // proc tady neni f(minSigned, arg1)?
                    return to_expr(*context, Z3_mk_bvashr(*context, maxSigned, arg1));
                }
                else if ((!flip && goal == UNSIGN_MAX) || (flip && goal == UNSIGN_MIN))
                {
                    if (isFreeVariable(e.arg(0))) {
                        appliedSubstitutions.push_back({e.arg(0), ones, false});
                    }
                    return ones;
                }
                else if ((!flip && goal == SIGN_MIN) || (flip && goal == SIGN_MAX))
                {
                    if (isFreeVariable(e.arg(0))) {
                        appliedSubstitutions.push_back({e.arg(0), minSigned, false});
                    }
                    return f(minSigned, arg1);
                }
                else if ((!flip && goal == UNSIGN_MIN) || (flip && goal == UNSIGN_MAX))
                {
                    if (isFreeVariable(e.arg(0))) {
                        appliedSubstitutions.push_back({e.arg(0), zero, false});
                    }
                    return zero;
                }
            }

            // can return precisely numbers with the same t+1 most-significant bits

            // (bvashr u t) -> (ite (or (= (bvand u (bvashr minSigned t)) 0)
            //                          (= (bvand u (bvashr minSigned t)) (bvashr minSigned t)))
            //                      u
            //                      0)

            auto onlyTopFromU = e.arg(0) & f(minSigned, e.arg(1));
            expr shiftarg1 = to_expr(*context, Z3_mk_bvshl(*context, (Z3_ast)e.arg(0), (Z3_ast)e.arg(1)));
            expr subst = z3::ite(onlyTopFromU == 0 || onlyTopFromU == f(minSigned, e.arg(1)),shiftarg1, zeroes);
            if(isFreeVariable(e.arg(0))) {
                appliedSubstitutions.push_back({e.arg(0), subst, false});
            }
            return z3::ite(onlyTopFromU == 0 || onlyTopFromU == f(minSigned, e.arg(1)),
                                      e.arg(0),
                                      zeroes);
	    }
	    else if (unconstrained1 && isBefore(e.arg(0), e.arg(1), boundVars, isPositive))
	    {
            int bvSize = e.arg(0).get_sort().bv_size();
	    	expr arg0 = e.arg(0);
    		expr ones = context->bv_val(-1, bvSize);
            expr zeroes = context->bv_val(0, bvSize);

            if (goalUnconstrained)
            {
                bool flip = (!isPositive && getBoundType(e.arg(1), boundVars) == EXISTENTIAL) ||
                    (isPositive && getBoundType(e.arg(1), boundVars) == UNIVERSAL);

                if ((!flip && goal == SIGN_MAX) || (flip && goal == SIGN_MIN))
                {
                    if (isFreeVariable(e.arg(1))) {
                        appliedSubstitutions.push_back({e.arg(1), z3::ite(arg0.extract(bvSize-1, bvSize-1) == 0, zero, ones), false});
                    }
                    return z3::ite(arg0.extract(bvSize-1, bvSize-1) == 0, arg0, ones);
                }
                else if ((!flip && goal == UNSIGN_MAX) || (flip && goal == UNSIGN_MIN))
                {
                    if (isFreeVariable(e.arg(1))) {
                        appliedSubstitutions.push_back({e.arg(1), z3::ite(arg0.extract(bvSize-1, bvSize-1) == 0, zero, ones), false});
                    }
                    return z3::ite(arg0.extract(bvSize-1, bvSize-1) == 0, arg0, ones);
                }
                else if ((!flip && goal == SIGN_MIN) || (flip && goal == SIGN_MAX))
                {
                    if (isFreeVariable(e.arg(1))) {
                        appliedSubstitutions.push_back({e.arg(1), z3::ite(arg0.extract(bvSize-1, bvSize-1) == 0, ones, zero), false});
                    }
                    return z3::ite(arg0.extract(bvSize-1, bvSize-1) == 0, zeroes, arg0);
                }
                else if ((!flip && goal == UNSIGN_MIN) || (flip && goal == UNSIGN_MAX))
                {
                    if (isFreeVariable(e.arg(1))) {
                        appliedSubstitutions.push_back({e.arg(1), z3::ite(arg0.extract(bvSize-1, bvSize-1) == 0, ones, zero), false});
                    }
                    return z3::ite(arg0.extract(bvSize-1, bvSize-1) == 0, zeroes, arg0);
                }
            }
	    }
	}
	else if (decl_kind == Z3_OP_BUREM_I)
	{
	    bool unconstrained0 = isUnconstrained(e.arg(0), boundVars);
	    bool unconstrained1 = isUnconstrained(e.arg(1), boundVars);

        int bvSize = e.arg(1).get_sort().bv_size();
        expr zero = context->bv_val(0, bvSize);
        expr one = context->bv_val(1, bvSize);
        expr ones = context->bv_val(-1, bvSize);

	    if (unconstrained0 && unconstrained1 &&
                getBoundType(e.arg(0), boundVars) == getBoundType(e.arg(1), boundVars))
	    {
		if (isBefore(e.arg(0), e.arg(1), boundVars, isPositive))
		{
            if(isFreeVariable(e.arg(0)) && isFreeVariable(e.arg(1))) {
                appliedSubstitutions.push_back({e.arg(1), zero, false});
                appliedSubstitutions.push_back({e.arg(0), e.arg(1), false});
            }
		    return e.arg(1);
		}
		else
		{
            if(isFreeVariable(e.arg(0)) && isFreeVariable(e.arg(1)))
                appliedSubstitutions.push_back({e.arg(1), zero, false});
		    return e.arg(0);
		}
	    }
	    else if (unconstrained0 && isBefore(e.arg(1), e.arg(0), boundVars, isPositive))
	    {
            if (goalUnconstrained)
            {
                bool flip = (!isPositive && getBoundType(e.arg(0), boundVars) == EXISTENTIAL) ||
                            (isPositive && getBoundType(e.arg(0), boundVars) == UNIVERSAL);

                if ((!flip && goal == UNSIGN_MIN) || (flip && goal == UNSIGN_MAX))
                {
                    if (isFreeVariable(e.arg(0))) {
                        appliedSubstitutions.push_back({e.arg(0), e.arg(0), false});
                    }
                    return zero;
                }
                else if ((!flip && goal == UNSIGN_MAX) || (flip && goal == UNSIGN_MIN))
                {
                    if (isFreeVariable(e.arg(0))) {
                        appliedSubstitutions.push_back({e.arg(0), e.arg(0) - 1, false});
                    }
                    return e.arg(0) - 1;
                }
                else if ((!flip && goal == SIGN_MIN) || (flip && goal == SIGN_MAX))
                {
                    auto minSigned = z3::concat(context->bv_val(1, 1), context->bv_val(0, bvSize - 1)); //1000...0
                    if (isFreeVariable(e.arg(0))) {
                        expr subst = z3::ite(e.arg(1).extract(bvSize-1, bvSize-1) == 0, e.arg(1), minSigned);
                        appliedSubstitutions.push_back({e.arg(0), subst, false});
                    }
                    return z3::ite(e.arg(1).extract(bvSize-1, bvSize-1) == 0, zero, minSigned);
                }
            }

            auto bvult = to_expr(*context, Z3_mk_bvult(*context, (Z3_ast)e.arg(0), (Z3_ast)e.arg(1)));

            // bvurem u t may return all values from {0,...,t-1}
            // (bvurem u t) -> (ite (= t 0) u (ite (bvult u t) u 0))
            if(isFreeVariable(e.arg(0)))
                appliedSubstitutions.push_back({e.arg(0), ite(bvult, e.arg(0), zero), false});

            return ite(e.arg(1) == zero,
                   e.arg(0),
                   ite(bvult, e.arg(0), zero));
	    }
        else if (unconstrained1 && isBefore(e.arg(0), e.arg(1), boundVars, isPositive))
	    {
            if (goalUnconstrained)
            {
                bool flip = (!isPositive && getBoundType(e.arg(1), boundVars) == EXISTENTIAL) ||
                    (isPositive && getBoundType(e.arg(1), boundVars) == UNIVERSAL);

                if ((!flip && goal == UNSIGN_MIN) || (flip && goal == UNSIGN_MAX))
                {
                    if (isFreeVariable(e.arg(1))) {
                        appliedSubstitutions.push_back({e.arg(1), one, false});
                    } // nerozumim komentáři
                    return zero; //by setting divisor to max
                }
                else if ((!flip && goal == UNSIGN_MAX) || (flip && goal == UNSIGN_MIN))
                {
                    if (isFreeVariable(e.arg(1))) {
                        appliedSubstitutions.push_back({e.arg(1), zero, false});
                    }
                    return e.arg(0); //by setting divisor to zero
                }
                else if ((!flip && goal == SIGN_MIN) || (flip && goal == SIGN_MAX))
                {
                    if (isFreeVariable(e.arg(1))) {
                        expr subst = z3::ite(e.arg(0).extract(bvSize-1, bvSize-1) == 0, one, ones);
                        appliedSubstitutions.push_back({e.arg(1), subst, false});
                    }
                    //unsigned division can not change positive sign to negative sign
                    //if positive, reduce to zero
                    //if negative, leave the same, because remainder will not decrease the negative number
                    return z3::ite(e.arg(0).extract(bvSize-1, bvSize-1) == 0, zero, e.arg(0));
                }
            }

            // bvurem t u may return all values from {0,...,(t-1)/2} \cup {t}
            // (bvurem t u) -> (ite (= t 0) 0 ((ite (bvule u (bvudiv (- t 1) 2)) u t)))
            auto bvule = to_expr(*context, Z3_mk_bvule(*context, e.arg(1),
                                                       Z3_mk_bvudiv(*context,
                                                                    (e.arg(0) - context->bv_val(1, bvSize)),
                                                                    context->bv_val(2, bvSize))));
            if(isFreeVariable(e.arg(1)))
                appliedSubstitutions.push_back({e.arg(1), z3::ite(bvule, e.arg(1) - e.arg(0), zero), false});

            auto result = z3::ite(e.arg(0) == 0, zero,
                                      z3::ite(bvule, e.arg(1), e.arg(0)));
            return result;
	    }
	}
	else if (decl_kind == Z3_OP_BUDIV_I)
	{
	    bool unconstrained0 = isUnconstrained(e.arg(0), boundVars);
	    bool unconstrained1 = isUnconstrained(e.arg(1), boundVars);

        int bvSize = e.arg(1).get_sort().bv_size();
        expr zero = context->bv_val(0, bvSize);
        expr one = context->bv_val(1, bvSize);
        expr two = context->bv_val(2, bvSize);
        expr ones = context->bv_val(-1, bvSize);
        expr zeroes = context->bv_val(0, bvSize);

	    if (unconstrained0 && unconstrained1 &&
                getBoundType(e.arg(0), boundVars) == getBoundType(e.arg(1), boundVars))
	    {
		if (isBefore(e.arg(0), e.arg(1), boundVars, isPositive))
		{
            if(isFreeVariable(e.arg(0)) && isFreeVariable(e.arg(1))) {
                appliedSubstitutions.push_back({e.arg(1), one, false});
                appliedSubstitutions.push_back({e.arg(0), e.arg(1), false});
            }
		    return e.arg(1);
		}
		else
		{
            if(isFreeVariable(e.arg(0)) && isFreeVariable(e.arg(1))) {
                appliedSubstitutions.push_back({e.arg(1), one, false});
            }
		    return e.arg(0);
		}
	    }

        if (unconstrained1 && isBefore(e.arg(0), e.arg(1), boundVars, isPositive) && goalUnconstrained)
            {
                bool flip = (!isPositive && getBoundType(e.arg(1), boundVars) == EXISTENTIAL) ||
                    (isPositive && getBoundType(e.arg(1), boundVars) == UNIVERSAL);

		        expr arg0 = e.arg(0);

                if ((!flip && goal == UNSIGN_MAX) || (flip && goal == UNSIGN_MIN))
                {
                    if (isFreeVariable(e.arg(1)))
                        appliedSubstitutions.push_back({e.arg(1), zero, false});
                    return ones;
                }
                else if ((!flip && goal == UNSIGN_MIN) || (flip && goal == UNSIGN_MAX))
                {
                    if (isFreeVariable(e.arg(1)))
                        appliedSubstitutions.push_back({e.arg(1), ones, false});
                    return z3::ite(arg0 == ones, context->bv_val(1, bvSize), zeroes);
                }
                else if ((!flip && goal == SIGN_MAX) || (flip && goal == SIGN_MIN))
                {
                    if (isFreeVariable(e.arg(1))) {
                        expr subst = z3::ite(e.arg(0).extract(bvSize - 1, bvSize - 1) == 0, one, two);
                        appliedSubstitutions.push_back({e.arg(1), subst, false});
                    }
                    //if positive, do not change, as unsigned division can not increase the number
                    //if negative, divide by 2 to get a positive number
                    return z3::ite(e.arg(0).extract(bvSize-1, bvSize-1) == 0, e.arg(0), f(arg0, 2));
                }
                else if ((!flip && goal == SIGN_MIN) || (flip && goal == SIGN_MAX))
                {
                    if (isFreeVariable(e.arg(1))) {
                        expr subst = z3::ite(e.arg(0).extract(bvSize - 1, bvSize - 1) == 0, zero,one);
                        appliedSubstitutions.push_back({e.arg(1), subst, false});
                    }
                    //if positive, reduce to -1
                    //if negative, do not change, as division would make it positive
                    return z3::ite(e.arg(0).extract(bvSize-1, bvSize-1) == 0, ones, arg0);
                }
            }

	    if (unconstrained0 && isBefore(e.arg(1), e.arg(0), boundVars, isPositive))
	    {
		    auto bvudiv = to_expr(*context, Z3_mk_bvudiv(*context, (Z3_ast)ones, e.arg(1)));
		    auto bvule = to_expr(*context, Z3_mk_bvule(*context, (Z3_ast)e.arg(0), bvudiv));

            if (goalUnconstrained)
            {
                bool flip = (!isPositive && getBoundType(e.arg(0), boundVars) == EXISTENTIAL) ||
                    (isPositive && getBoundType(e.arg(0), boundVars) == UNIVERSAL);

                if ((!flip && goal == UNSIGN_MIN) || (flip && goal == UNSIGN_MAX))
                {
                    if (isFreeVariable(e.arg(0))) {
                        appliedSubstitutions.push_back({e.arg(0), zero, false});
                    }
                    return z3::ite(e.arg(1) == zero, ones, zero);
                }
                else if ((!flip && goal == UNSIGN_MAX) || (flip && goal == UNSIGN_MIN))
                {
                    if (isFreeVariable(e.arg(0))) {
                        appliedSubstitutions.push_back({e.arg(0), ones, false});
                    }
                    return z3::ite(e.arg(1) == zero, ones, bvudiv); // for a/0, the max is 11..1, for a/b it is 11...1/b
                }
                else if ((!flip && goal == SIGN_MIN) || (flip && goal == SIGN_MAX))
                {
                    auto minSigned = z3::concat(context->bv_val(1, 1), context->bv_val(0, bvSize - 1)); //1000...0
                    if (isFreeVariable(e.arg(0))) {
                        expr subst = z3::ite(e.arg(1) == one,
                                             minSigned,
                                             zero);
                        appliedSubstitutions.push_back({e.arg(0), subst, false});
                    }
                    return z3::ite(e.arg(1) == zero,
                                   ones,
                                   z3::ite(e.arg(1) == one,
                                           minSigned,
                                           zero));
                }
                else if ((!flip && goal == SIGN_MAX) || (flip && goal == SIGN_MIN))
                {
                    auto maxSigned = concat(context->bv_val(0, 1), context->bv_val(-1, bvSize - 1));
                    if (isFreeVariable(e.arg(0))) {
                        expr subst = z3::ite(e.arg(1) == one,
                                             maxSigned,
                                             ones);
                        appliedSubstitutions.push_back({e.arg(0), subst, false});
                    }
                    return z3::ite(e.arg(1) == zero,
                                   ones,
                                   z3::ite(e.arg(1) == one,
                                           maxSigned,
                                           bvudiv));
                }
            }

            // bvurem may return all values from {0,...,(2^32-1)/t}
            // (bvurem u t) -> (ite (= t 0) (11...1) (ite (bvule u (bvudiv (11...1)/t)) u 0))

            if(isFreeVariable(e.arg(0))) {
                appliedSubstitutions.push_back({e.arg(0), ite(bvule, e.arg(1) * e.arg(0), zero), false});
            }
            return ite(e.arg(1) == zero,
                   ones,
                   ite(bvule, e.arg(0), zero));
	    }
	}
	else if (decl_kind == Z3_OP_OR)
	{
	    auto toReturn = context->bool_val(false);

	    std::vector<expr> toReturnVec;
	    bool changed = false;

	    for (unsigned int i = 0; i < num; i++)
	    {
            if (isUnconstrained(e.arg(i), boundVars))
            {
                auto boundType = getBoundType(e.arg(i), boundVars);
                if ((boundType == EXISTENTIAL && isPositive) || (boundType == UNIVERSAL && !isPositive))
                {
                    if (isFreeVariable(e.arg(i))) {
                        appliedSubstitutions.push_back({e.arg(0), context->bool_val(true), false});
                    }
                    return context->bool_val(true);
                }
                if (isFreeVariable(e.arg(i))) {
                    appliedSubstitutions.push_back({e.arg(0), context->bool_val(false), false});
                }
                changed = true;
            }
            else
            {
                toReturnVec.push_back(e.arg(i));
            }
	    }

	    if (changed)
	    {
            for (auto const &toReturnPart : toReturnVec)
            {
                toReturn = toReturn || toReturnPart;
            }
		return toReturn;
	    }
	}
	else if (decl_kind == Z3_OP_AND)
	{
	    auto toReturn = context->bool_val(true);

	    std::vector<expr> toReturnVec;
	    bool changed = false;

	    for (unsigned int i = 0; i < num; i++)
	    {
            if (isUnconstrained(e.arg(i), boundVars))
            {
                auto boundType = getBoundType(e.arg(i), boundVars);
                if ((boundType == EXISTENTIAL && !isPositive) || (boundType == UNIVERSAL && isPositive))
                {
                    if (isFreeVariable(e.arg(i))) {
                        appliedSubstitutions.push_back({e.arg(0), context->bool_val(false), false});
                    }
                    return context->bool_val(false);
                }
                if (isFreeVariable(e.arg(i))){
                    appliedSubstitutions.push_back({e.arg(0), context->bool_val(true), false});
                }
                changed = true;
            }
            else
            {
                toReturnVec.push_back(e.arg(i));
            }
	    }

	    if (changed)
	    {
            for (auto const &toReturnPart : toReturnVec)
            {
                toReturn = toReturn && toReturnPart;
            }

            return toReturn;
	    }
	}
	else if (decl_kind == Z3_OP_IFF)
	{
	    return e;
//			return ((simplifyOnce(e.arg(0), boundVars, isPositive) || !simplifyOnce(e.arg(1), boundVars, !isPositive)) &&
//					(!simplifyOnce(e.arg(0), boundVars, !isPositive) || simplifyOnce(e.arg(1), boundVars, isPositive)));
	}
    else if (decl_kind == Z3_OP_NOT)
	{
	    if (isUnconstrained(e.arg(0), boundVars))
	    {
            if (isFreeVariable(e.arg(0)))
                appliedSubstitutions.push_back({e.arg(0), e, false});
		    return e.arg(0);
	    }
	}
	else if (decl_kind == Z3_OP_EQ) {
        if (isUnconstrained(e.arg(0), boundVars) && isBefore(e.arg(1), e.arg(0), boundVars, isPositive)) {
            auto boundType = getBoundType(e.arg(0), boundVars);

            if (boundType == EXISTENTIAL) {
                if (isFreeVariable(e.arg(0))) {
                    if (isPositive) {
                        appliedSubstitutions.push_back({e.arg(0), e.arg(1), false});
                    } else {
                        expr subst = e;
                        if (e.arg(1).is_bool())
                            subst = !e.arg(1);
                        else {
                            int bvSize = e.arg(1).get_sort().bv_size();
                            expr one = context->bv_val(1, bvSize);
                            subst = to_expr(*context, Z3_mk_bvadd(*context, e.arg(1), one));
                        }
                        appliedSubstitutions.push_back({e.arg(0), subst, false});
                    }
                }
                return isPositive ? context->bool_val(true) : context->bool_val(false);
            } else {
                return isPositive ? context->bool_val(false) : context->bool_val(true);
            }
        } else if (isUnconstrained(e.arg(1), boundVars) && isBefore(e.arg(0), e.arg(1), boundVars, isPositive)) {
            auto boundType = getBoundType(e.arg(1), boundVars);

            if (boundType == EXISTENTIAL) {
                if (isFreeVariable(e.arg(1))) {
                    if (isPositive) {
                        appliedSubstitutions.push_back({e.arg(1), e.arg(0), false});
                    } else {
                        expr subst = e;
                        if (e.arg(0).is_bool())
                            subst = !e.arg(0);
                        else {
                            int bvSize = e.arg(1).get_sort().bv_size();
                            expr one = context->bv_val(1, bvSize);
                            subst = to_expr(*context, Z3_mk_bvadd(*context, e.arg(0), one));
                        }
                        appliedSubstitutions.push_back({e.arg(1), subst, false});
                    }
                }
                return isPositive ? context->bool_val(true) : context->bool_val(false);
            } else {
                return isPositive ? context->bool_val(false) : context->bool_val(true);
            }
        } else {
            if (e.arg(0).is_bool()) {
                return e; //or split into implications
            } else {
                return simplifyOnce(e.arg(0), boundVars, isPositive) == simplifyOnce(e.arg(1), boundVars, isPositive);
            }
        }
    }
	else if (decl_kind == Z3_OP_SLEQ || decl_kind == Z3_OP_ULEQ )
	{
        auto bvSize = e.arg(1).get_sort().bv_size();
        auto maxValue = decl_kind == Z3_OP_SLEQ ?
                        concat(context->bv_val(0, 1), context->bv_val(-1, bvSize - 1)) :
                        context->bv_val(-1, bvSize);
        auto minValue = decl_kind == Z3_OP_SLEQ ?
                        concat(context->bv_val(1, 1), context->bv_val(0, bvSize - 1)) :
                        context->bv_val(0, bvSize);

	    if (isUnconstrained(e.arg(0), boundVars) && isBefore(e.arg(1), e.arg(0), boundVars, isPositive))
	    {
            auto boundType = getBoundType(e.arg(0), boundVars);

            if (boundType == EXISTENTIAL)
            {
                if (isFreeVariable(e.arg(0))) {
                    if (isPositive) {
                        appliedSubstitutions.push_back({e.arg(0), minValue, false});
                    } else {
                        appliedSubstitutions.push_back({e.arg(0), maxValue, false});
                    }
                }
                return isPositive ? context->bool_val(true) : e.arg(1) == maxValue;
            }
            else
            {
                return isPositive ? e.arg(1) == maxValue : context->bool_val(true);
            }
	    }
	    else if (isUnconstrained(e.arg(1), boundVars) && isBefore(e.arg(0), e.arg(1), boundVars, isPositive))
	    {
            auto boundType = getBoundType(e.arg(1), boundVars);

            if (boundType == EXISTENTIAL)
            {
                if (isFreeVariable(e.arg(1))) {
                    if (isPositive) {
                        appliedSubstitutions.push_back({e.arg(1), maxValue, false});
                    } else {
                        appliedSubstitutions.push_back({e.arg(1), minValue, false});
                    }
                }
                return isPositive ? context->bool_val(true) : e.arg(0) == minValue;
            }
            else
            {
                return isPositive ? e.arg(0) == minValue : context->bool_val(true);
            }
	    }

        auto arg0 = simplifyOnce(e.arg(0), boundVars, isPositive, decl_kind == Z3_OP_SLEQ ? SIGN_MIN : UNSIGN_MIN);
        auto arg1 = simplifyOnce(e.arg(1), boundVars, isPositive, decl_kind == Z3_OP_SLEQ ? SIGN_MAX : UNSIGN_MAX);

        return f(arg0, arg1);
	}
	else if (decl_kind == Z3_OP_SLT || decl_kind == Z3_OP_ULT)
	{
        auto bvSize = e.arg(1).get_sort().bv_size();

        auto minValue = decl_kind == Z3_OP_SLT ?
                        concat(context->bv_val(1, 1), context->bv_val(0, bvSize - 1)) :
                        context->bv_val(0, bvSize);
        auto maxValue = decl_kind == Z3_OP_SLT ?
                        concat(context->bv_val(0, 1), context->bv_val(-1, bvSize - 1)) :
                        context->bv_val(-1, bvSize);

	    if (isUnconstrained(e.arg(0), boundVars) && isBefore(e.arg(1), e.arg(0), boundVars, isPositive))
	    {
		auto boundType = getBoundType(e.arg(0), boundVars);

		if (boundType == EXISTENTIAL)
		{
            if (isFreeVariable(e.arg(0))) {
                if (isPositive) {
                    appliedSubstitutions.push_back({e.arg(0), minValue, false});
                } else {
                    appliedSubstitutions.push_back({e.arg(0), maxValue, false});
                }
            }
		    return isPositive ? !(e.arg(1) == minValue) : context->bool_val(false);
		}
		else
		{
		    return isPositive ? context->bool_val(false) : !(e.arg(1) == minValue);
		}
	    }
	    else if (isUnconstrained(e.arg(1), boundVars) && isBefore(e.arg(0), e.arg(1), boundVars, isPositive))
	    {
            auto boundType = getBoundType(e.arg(1), boundVars);

            if (boundType == EXISTENTIAL)
            {
                if (isFreeVariable(e.arg(1))) {
                    if (isPositive) {
                        appliedSubstitutions.push_back({e.arg(1), maxValue, false});
                    } else {
                        appliedSubstitutions.push_back({e.arg(1), minValue, false});
                    }
                }
                return isPositive ? !(e.arg(0) == maxValue) : context->bool_val(false);
            }
            else
            {
                return isPositive ? context->bool_val(false) : !(e.arg(0) == maxValue);
            }
	    }

        auto arg0 = simplifyOnce(e.arg(0), boundVars, isPositive, decl_kind == Z3_OP_SLT ? SIGN_MIN : UNSIGN_MIN);
        auto arg1 = simplifyOnce(e.arg(1), boundVars, isPositive, decl_kind == Z3_OP_SLT ? SIGN_MAX : UNSIGN_MAX);

        return f(arg0, arg1);
	}
	else if (decl_kind == Z3_OP_ITE)
	{
        if (isUnconstrained(e.arg(0), boundVars) && isUnconstrained(e.arg(1), boundVars) && getBoundType(e.arg(0), boundVars) == getBoundType(e.arg(1), boundVars))
        {
            if (isFreeVariable(e.arg(0)))
                appliedSubstitutions.push_back({e.arg(0), context->bool_val(true), false});
            return e.arg(1);
        }

        if (isUnconstrained(e.arg(0), boundVars) && isUnconstrained(e.arg(2), boundVars) && getBoundType(e.arg(0), boundVars) == getBoundType(e.arg(2), boundVars))
        {
            if (isFreeVariable(e.arg(0)))
                appliedSubstitutions.push_back({e.arg(0), context->bool_val(true), false});
            return e.arg(2);
        }

	    auto result = ite(e.arg(0), simplifyOnce(e.arg(1), boundVars, isPositive), simplifyOnce(e.arg(2), boundVars, isPositive));
	    if (isPositive)
	    {
		    trueSimplificationCache.insert({e, {result, boundVars}});
	    }
	    else
	    {
		    falseSimplificationCache.insert({e, {result, boundVars}});
	    }
	    return result;
	}


	expr_vector arguments(*context);
	for (unsigned int i = 0; i < num; i++)
	{
	    if (decl_kind == Z3_OP_NOT)
	    {
		arguments.push_back(simplifyOnce(e.arg(i), boundVars, !isPositive));
	    }
	    else
	    {
		arguments.push_back(simplifyOnce(e.arg(i), boundVars, isPositive));
	    }
	}

	auto result = f(arguments);
	if (isPositive)
	{
	    trueSimplificationCache.insert({e, {result, boundVars}});
	}
	else
	{
	    falseSimplificationCache.insert({e, {result, boundVars}});
	}

	return result;
    }
    else if (e.is_quantifier())
    {
	Z3_ast ast = (Z3_ast)e;

	int numBound = Z3_get_quantifier_num_bound(*context, ast);
	BoundType boundType;

	if (isPositive)
	{
	    boundType = Z3_is_quantifier_forall(*context, ast) ? UNIVERSAL : EXISTENTIAL;
	}
	else
	{
	    boundType = Z3_is_quantifier_forall(*context, ast) ? EXISTENTIAL : UNIVERSAL;
	}

	for (int i = 0; i < numBound; i++)
	{
	    Z3_symbol z3_symbol = Z3_get_quantifier_bound_name(*context, ast, i);

	    symbol current_symbol(*context, z3_symbol);

	    int level;
	    if (boundVars.size() == 0)
	    {
		level = 1;
	    }
	    else
	    {
		auto previousVar = boundVars.back();
		level = std::get<2>(previousVar);

		if (boundType != std::get<1>(previousVar))
		{
		    level++;
		}
	    }


	    boundVars.push_back(make_tuple(current_symbol.str(), boundType, level));
	}

	Z3_sort sorts [numBound];
	Z3_symbol decl_names [numBound];
	for (int i = 0; i < numBound; i++)
	{
	    sorts[i] = Z3_get_quantifier_bound_sort(*context, ast, i);
	    decl_names[i] = Z3_get_quantifier_bound_name(*context, ast, i);
	}

	Z3_ast quantAst = Z3_mk_quantifier(
	    *context,
	    Z3_is_quantifier_forall(*context, ast),
	    Z3_get_quantifier_weight(*context, ast),
	    0,
	    {},
	    numBound,
	    sorts,
	    decl_names,
	    (Z3_ast)simplifyOnce(e.body(), boundVars, isPositive));
	auto result = to_expr(*context, quantAst);
	return result;
    }

    if (isPositive)
    {
	trueSimplificationCache.insert({e, {e, boundVars}});
    }
    else
    {
	falseSimplificationCache.insert({e, {e, boundVars}});
    }
    return e;
}

void UnconstrainedVariableSimplifier::ReconstructModel(Model &model)
{
    for (auto it = appliedSubstitutions.rbegin(); it != appliedSubstitutions.rend(); it++) {
        const auto &[var, subst, isMul] = *it;

        std::stringstream variableString;
        variableString << var;

        nullVarsWithoutModel(model, subst);
        if (var.is_app() && var.decl().decl_kind() == Z3_OP_EXTRACT){
            variableString << var.arg(0);
            cout<<"mys"<<flush;
            auto repa = subst.get_numeral_int();

            Z3_func_decl z3decl = (Z3_func_decl)var.decl();
            int bitFrom = Z3_get_decl_int_parameter(*context, z3decl, 1);
            repa = repa << bitFrom;

            int bvSize = var.arg(0).get_sort().bv_size();
            model[variableString.str()] = vectorFromNumeral(context->bv_val(repa, bvSize));

        }
        else if (isMul){
            model[variableString.str()] = ReconstructModelForMul(model, subst, var);
        }
        else {
            model[variableString.str()] = vectorFromNumeral(substituteModel(subst, model));
        }
    }

}

bool UnconstrainedVariableSimplifier::isUnconstrained(expr e, const vector<BoundVar> &boundVars) const
{
    if (!isVar(e) && e.is_app())
    {
	return e.decl().decl_kind() == Z3_OP_EXTRACT && isUnconstrained(e.arg(0), boundVars);
    }

    if (e.is_var())
    {
	Z3_ast ast = (Z3_ast)e;
	int deBruijnIndex = Z3_get_index_value(*context, ast);
	return (variableCounts.at(std::get<0>(boundVars.at(boundVars.size() - deBruijnIndex - 1))) == 1);
    }
    else if (e.is_app() && !e.is_numeral())
    {
	func_decl f = e.decl();
	unsigned num = e.num_args();

	if (num == 0 && f.name() != NULL)
	{
	    stringstream ss;
	    ss << e;

            if (forcedConstrained.find(ss.str()) != forcedConstrained.end())
            {
                return false;
            }

	    if (ss.str() != "true" && ss.str() != "false")
	    {
		return (variableCounts.at(e.decl().name().str()) == 1);
	    }
	}
    }

    return false;
}

bool UnconstrainedVariableSimplifier::isVar(expr e) const
{
    if (e.is_var())
    {
	return true;
    }
    else if (e.is_app() || e.is_numeral())
    {
	func_decl f = e.decl();
	unsigned num = e.num_args();

	if (num == 0 && f.name() != NULL)
	{
	    return true;
	}
    }

    return false;
}

int UnconstrainedVariableSimplifier::getMaxLevel(expr e, const std::vector<BoundVar> &boundVars, bool isPositive = true)
{
    auto item = subformulaMaxLevels.find({e, boundVars});
    if (item != subformulaMaxLevels.end())
    {
	return item->second;
    }

    if (e.is_var())
    {
	Z3_ast ast = (Z3_ast)e;
	int deBruijnIndex = Z3_get_index_value(*context, ast);
	return std::get<2>(boundVars[boundVars.size() - deBruijnIndex - 1]);
    }
    else if (e.is_const() && !e.is_numeral())
    {
	return -1;
    }
    else if (e.is_app())
    {
	func_decl f = e.decl();
	unsigned num = e.num_args();

	int maxLevel = -1;

	if (num != 0)
	{
	    for (unsigned i = 0; i < num; i++)
	    {
		auto currentMaxLevel = getMaxLevel(e.arg(i), boundVars, isPositive);

		if (currentMaxLevel > maxLevel)
		{
		    maxLevel = currentMaxLevel;
		}
	    }

	    subformulaMaxLevels.insert({{e, boundVars}, maxLevel});
	    return maxLevel;
	}
	else if (f.name() != NULL)
	{
	    return -1;
	}
    }
    else if(e.is_quantifier())
    {
	Z3_ast ast = (Z3_ast)e;
	int numBound = Z3_get_quantifier_num_bound(*context, ast);
	BoundType boundType;

	if (isPositive)
	{
	    boundType = Z3_is_quantifier_forall(*context, ast) ? UNIVERSAL : EXISTENTIAL;
	}
	else
	{
	    boundType = Z3_is_quantifier_forall(*context, ast) ? EXISTENTIAL : UNIVERSAL;
	}

	int level;
	if (boundVars.size() == 0)
	{
	    level = 1;
	}
	else
	{
	    auto previousVar = boundVars.back();
	    level = std::get<2>(previousVar);

	    if (boundType != std::get<1>(previousVar))
	    {
		level++;
	    }
	}

	vector<BoundVar> newBoundVars = boundVars;

	for (int i = 0; i < numBound; i++)
	{
	    Z3_symbol z3_symbol = Z3_get_quantifier_bound_name(*context, ast, i);
	    symbol current_symbol(*context, z3_symbol);

	    newBoundVars.push_back(make_tuple(current_symbol.str(), boundType, level));
	}

	return getMaxLevel(e.body(), newBoundVars, isPositive);
    }

    assert(false);
    return -1;
}

//should be true if all variables in "a" are quantified before a variable "b"
bool UnconstrainedVariableSimplifier::isBefore(expr a, expr b, const std::vector<BoundVar> &boundVars, bool isPositive)
{
    int aLevel = getMaxLevel(a, boundVars, isPositive);
    int bLevel = getMaxLevel(b, boundVars, isPositive);

    return (aLevel <= bLevel);
}

bool UnconstrainedVariableSimplifier::isFreeVariable(expr e)
{
    return (e.is_app() && e.num_args() == 0 && e.decl().name() != NULL) || (e.is_app() && e.decl().decl_kind() == Z3_OP_EXTRACT &&
            isFreeVariable(e.arg(0)));
}

BoundType UnconstrainedVariableSimplifier::getBoundType(expr e, const std::vector<BoundVar> &boundVars)
{
    if (e.is_var())
    {
	Z3_ast ast = (Z3_ast)e;
	int deBruijnIndex = Z3_get_index_value(*context, ast);
	return std::get<1>(boundVars[boundVars.size() - deBruijnIndex - 1]);
    }
    else if (e.is_app())
    {
	func_decl f = e.decl();

	unsigned num = e.num_args();

	if (f.decl_kind() == Z3_OP_EXTRACT)
	{
	    return getBoundType(e.arg(0), boundVars);
	}

	if (num == 0 && f.name() != NULL)
	{
	    return EXISTENTIAL;
	}
    }

    std::cout << e << std::endl;
    assert(false);
    return EXISTENTIAL;
}

int UnconstrainedVariableSimplifier::getNumberOfLeadingZeroes(const z3::expr &e)
{
    assert(e.is_numeral());

    std::stringstream ss;
    ss << e;

    string numeralString = ss.str();

    int bitSize = e.get_sort().bv_size();

    const string prefix = numeralString.substr(0, 2);
    string valueString = numeralString.substr(2);

    assert(prefix == "#x" || prefix == "#b");

    std::size_t found = valueString.find_last_not_of("0");

    if (prefix == "#b")
    {
	if (found == std::string::npos)
	{
	    return bitSize;
	}
	else
	{
	    return bitSize - found - 1;
	}
    }
    else
    {
	if (found == std::string::npos)
	{
	    return bitSize;
	}
	else
	{
	    int zeroes = bitSize - (found + 1)*4;

	    switch (valueString[found])
	    {
	    case '2':
	    case '6':
	    case 'a':
	    case 'e':
		return zeroes + 1;
	    case '4':
	    case 'c':
		return zeroes + 2;
	    case '8':
		return zeroes + 3;
	    default:
		return zeroes;
	    }
	}

    }
}

void UnconstrainedVariableSimplifier::addCounts(const std::map<std::string, int>& from, std::map<std::string, int> &to)
{
    for (auto &item : from)
    {
	auto singleVarCount = to.find(item.first);
	if (singleVarCount == to.end())
	{
	    to[item.first] = item.second;
	}
	else
	{
	    if (to[item.first] == 2)
	    {
		continue;
	    }

	    if (singleVarCount->second + item.second > 1)
	    {
		to[item.first] = 2;
	    }
	    else
	    {
		to[item.first] = singleVarCount->second + item.second;
	    }
	}
    }
}

void UnconstrainedVariableSimplifier::maxCounts(std::map<std::string, int>&& from, std::map<std::string, int> &to)
{
    for (auto &item : from)
    {
	auto singleVarCount = to.find(item.first);
	if (singleVarCount == to.end())
	{
	    to[item.first] = item.second;
	}
	else
	{
	    to[item.first] = std::max(singleVarCount->second, item.second);
	}
    }
}

std::map<std::string, int> UnconstrainedVariableSimplifier::countFormulaVarOccurences(z3::expr e)
{
    if (e.is_app() && e.decl().decl_kind() == Z3_OP_OR)
    {
	assert(e.num_args() > 0);
	auto variableCounts = countVariableOccurences(e.arg(0), true);
	for(unsigned int i = 1; i < e.num_args(); i++)
	{
	    maxCounts(countVariableOccurences(e.arg(i), true), variableCounts);
	}
	return variableCounts;
    }

    return countVariableOccurences(e, true);
}

expr UnconstrainedVariableSimplifier::ReconstructModelForMul(Model &model, expr subst, expr var) {
    int bvSize = subst.get_sort().bv_size();
    expr zero = context->bv_val(0, bvSize);
    expr e = substituteModel(subst, model);
    int numOfZeroes = 0;
    auto bitVector = get<vector<bool>>(vectorFromNumeral(e));
    for (auto iter = bitVector.rbegin(); iter != bitVector.rend(); iter++) {
        auto fabia = *iter;
        if (fabia == 0){
            numOfZeroes++;
        }
        else {
            break;
        }
    }

    long int i = e.get_numeral_int64();
    long int shifted = i >> numOfZeroes;
    long int mod = 1L << bvSize;
    long int inverse = mod_inverse(shifted, mod);

    auto zeroes = context->bv_val(numOfZeroes, bvSize);
    auto inv = context->bv_val(inverse, bvSize);
    return to_expr(*context, Z3_mk_bvmul(*context, Z3_mk_bvlshr(*context, var, zeroes),inv));
}

void UnconstrainedVariableSimplifier::nullVarsWithoutModel(Model &model, expr subst) {
    expr e = substituteModel(subst, model);
    auto varOccurences = countFormulaVarOccurences(e);

    for (auto iterator = varOccurences.rbegin(); iterator != varOccurences.rend(); iterator++) {
        const auto &[variable, occ] = *iterator;
        std::stringstream varStr;
        varStr << variable;
        if (subst.is_bool()) {
            model[varStr.str()] = true;
        }
        else {
            int bvSize = subst.get_sort().bv_size();
            expr zero = context->bv_val(0, bvSize);
            model[varStr.str()] = vectorFromNumeral(zero);
        }
    }
}
