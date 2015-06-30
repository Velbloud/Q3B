#include "ExprSimplifier.h"
#include <string>
#include <sstream>

using namespace z3;

expr ExprSimplifier::Simplify(const expr &e)
{
    if (e.is_app())
    {
        func_decl dec = e.decl();

        if (dec.name().str() == "and")
        {
            //std::cout << "simplifying top-level and" << std::endl;
            int argsCount = e.num_args();

            for (int i=0; i < argsCount; i++)
            {
                expr variable(*context);
                expr replacement(*context);
                if (getSubstitutableEquality(e.arg(i), &variable, &replacement))
                {
                    //std::cout << "substitutable equality found: " << e.arg(i) << std::endl;

                    Z3_ast args [argsCount-1];

                    for (int j=0; j < argsCount-1; j++)
                    {
                        if (j < i)
                        {
                            args[j] = (Z3_ast)e.arg(j);
                        }
                        else
                        {
                            args[j] = (Z3_ast)e.arg(j+1);
                        }
                    }                   

                    expr withoutSubstitutedEquality = to_expr(*context, Z3_mk_and(*context, argsCount - 1, args));

                    expr_vector src(*context);
                    expr_vector dst(*context);

                    //std::cout << "withoutSubstituted: " << withoutSubstitutedEquality << std::endl;
                    src.push_back(variable);
                    dst.push_back(replacement);

                    expr substituted = withoutSubstitutedEquality.substitute(src, dst);
                    //std::cout << "substituted: " << substituted << std::endl;

                    return Simplify(substituted);
                }
            }

            std::cout << "nothing done" << std::endl;

            return e;
        }
    }

    return e;
}

expr ExprSimplifier::PushQuantifierIrrelevantSubformulas(const expr &e)
{
    if (!e.get_sort().is_bool())
    {
        return e;
    }

    if (e.is_app())
    {
        func_decl dec = e.decl();
        int numArgs = e.num_args();

        expr_vector arguments(*context);
        for (int i = 0; i < numArgs; i++)
        {
            arguments.push_back(PushQuantifierIrrelevantSubformulas(e.arg(i)));
        }

        return dec(arguments);
    }
    else if (e.is_quantifier())
    {
        Z3_ast ast = (Z3_ast)e;

        int numBound = Z3_get_quantifier_num_bound(*context, ast);
        //expr_vector bound(*context);
        Z3_sort sorts [numBound];
        Z3_symbol decl_names [numBound];
        for (int i = 0; i < numBound; i++)
        {
            sorts[i] = Z3_get_quantifier_bound_sort(*context, ast, i);
            decl_names[i] = Z3_get_quantifier_bound_name(*context, ast, i);
            //Z3_get_quantifier_bound_name()
            //bound.push_back(e.arg(i));
        }

        if (e.body().is_app())
        {
            func_decl innerDecl = e.body().decl();

            expr_vector bodyVector(*context);
            expr_vector replacementVector(*context);

            if (innerDecl.decl_kind() == Z3_OP_AND || innerDecl.decl_kind() == Z3_OP_OR)
            {
                int numInnerArgs = e.body().num_args();
                for (int i = 0; i < numInnerArgs; i++)
                {
                    expr arg = e.body().arg(i);
                    bool relevant = isRelevant(arg, numBound, 0);

                    if (!relevant)
                    {
                        replacementVector.push_back(decreaseDeBruijnIndices(arg, numBound, -1));
                    }
                    else
                    {
                        bodyVector.push_back(arg);
                    }
                }

                expr bodyExpr = innerDecl(bodyVector);
                Z3_ast quantAst = Z3_mk_quantifier(
                            *context,
                            Z3_is_quantifier_forall(*context, ast),
                            Z3_get_quantifier_weight(*context, ast),
                            0,
                            {},
                            numBound,
                            sorts,
                            decl_names,
                            (Z3_ast)PushQuantifierIrrelevantSubformulas(bodyExpr));

                replacementVector.push_back(to_expr(*context, quantAst));
                return innerDecl(replacementVector);
            }
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
                    (Z3_ast)PushQuantifierIrrelevantSubformulas(e.body()));
        return to_expr(*context, quantAst);
    }
    else
    {
        return e;
    }
}

expr ExprSimplifier::RefinedPushQuantifierIrrelevantSubformulas(const expr &e)
{
    if (!e.get_sort().is_bool())
    {
        return e;
    }

    if (e.is_app())
    {
        func_decl dec = e.decl();
        int numArgs = e.num_args();

        expr_vector arguments(*context);
        for (int i = 0; i < numArgs; i++)
        {
            arguments.push_back(RefinedPushQuantifierIrrelevantSubformulas(e.arg(i)));
        }

        return dec(arguments);
    }
    else if (e.is_quantifier())
    {
        Z3_ast ast = (Z3_ast)e;

        int numBound = Z3_get_quantifier_num_bound(*context, ast);
        //expr_vector bound(*context);
        Z3_sort sorts [numBound];
        Z3_symbol decl_names [numBound];
        for (int i = 0; i < numBound; i++)
        {
            sorts[i] = Z3_get_quantifier_bound_sort(*context, ast, i);
            decl_names[i] = Z3_get_quantifier_bound_name(*context, ast, i);
            //Z3_get_quantifier_bound_name()
            //bound.push_back(e.arg(i));
        }

        if (e.body().is_app())
        {
            func_decl innerDecl = e.body().decl();

            expr_vector bodyVector(*context);
            expr_vector replacementVector(*context);

            if (innerDecl.decl_kind() == Z3_OP_AND || innerDecl.decl_kind() == Z3_OP_OR)
            {
                int numInnerArgs = e.body().num_args();

                for (int i = 0; i < numInnerArgs; i++)
                {
                    expr arg = e.body().arg(i);
                    bool relevant = isRelevant(arg, 1, 0);

                    if (!relevant)
                    {
                        replacementVector.push_back(decreaseDeBruijnIndices(arg, 1, -1));
                    }
                    else
                    {
                        bodyVector.push_back(arg);
                    }
                }

                Z3_sort outerSorts [numBound-1];
                Z3_symbol outerDecl_names [numBound-1];
                for (int i = 0; i < numBound-1; i++)
                {
                    outerSorts[i] = sorts[i];
                    outerDecl_names[i] = decl_names[i];
                }

                Z3_sort innerSorts [1];
                Z3_symbol innerDecl_names [1];
                innerSorts[0] = sorts[numBound-1];
                innerDecl_names[0] = decl_names[numBound-1];

                expr bodyExpr = innerDecl(bodyVector);
                Z3_ast innerQuantAst = Z3_mk_quantifier(
                            *context,
                            Z3_is_quantifier_forall(*context, ast),
                            Z3_get_quantifier_weight(*context, ast),
                            0,
                            {},
                            1,
                            innerSorts,
                            innerDecl_names,
                            (Z3_ast)RefinedPushQuantifierIrrelevantSubformulas(bodyExpr));

                replacementVector.push_back(to_expr(*context, innerQuantAst));
                expr outerBody = innerDecl(replacementVector);
                std::cout << outerBody << std::endl;

                if (numBound == 1)
                {
                    return outerBody;
                }
                else
                {
                    Z3_ast outerQuantAst = Z3_mk_quantifier(
                                *context,
                                Z3_is_quantifier_forall(*context, ast),
                                Z3_get_quantifier_weight(*context, ast),
                                0,
                                {},
                                numBound-1,
                                outerSorts,
                                outerDecl_names,
                                (Z3_ast)outerBody);
                    return to_expr(*context, outerQuantAst);
                }
            }
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
                    (Z3_ast)RefinedPushQuantifierIrrelevantSubformulas(e.body()));
        return to_expr(*context, quantAst);
    }
    else
    {
        return e;
    }
}

bool ExprSimplifier::getSubstitutableEquality(const expr &e, expr *variable, expr *replacement)
{
    if (e.is_app())
    {
        func_decl dec = e.decl();

        if (dec.name().str() == "=")
        {
            expr firstArg = e.arg(0);
            if (firstArg.is_app() && firstArg.num_args() == 0 && firstArg.decl().name() != NULL && firstArg.is_bv() && !firstArg.is_numeral())
            {
                *variable = firstArg;
                *replacement = e.arg(1);
                return true;
            }
        }
    }

    return false;
}

expr ExprSimplifier::decreaseDeBruijnIndices(const expr &e, int decreaseBy, int leastIndexToDecrease)
{
    if (e.is_var())
    {
        Z3_ast ast = (Z3_ast)e;
        int deBruijnIndex = Z3_get_index_value(*context, ast);

        if (deBruijnIndex > leastIndexToDecrease)
        {
            return to_expr(*context, Z3_mk_bound(*context, deBruijnIndex - decreaseBy, (Z3_sort)e.get_sort()));
        }
        else
        {
            return e;
        }
    }
    else if (e.is_app())
    {
        func_decl dec = e.decl();
        int numArgs = e.num_args();

        expr_vector arguments(*context);
        for (int i = 0; i < numArgs; i++)
        {
            arguments.push_back(decreaseDeBruijnIndices(e.arg(i), decreaseBy, leastIndexToDecrease));
        }

        return dec(arguments);
    }
    else if (e.is_quantifier())
    {
        Z3_ast ast = (Z3_ast)e;

        int numBound = Z3_get_quantifier_num_bound(*context, ast);

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
                    (Z3_ast)decreaseDeBruijnIndices(e.body(), decreaseBy, leastIndexToDecrease + numBound));
        return to_expr(*context, quantAst);
    }
    else
    {
        return e;
    }
}

expr ExprSimplifier::negate(const expr e)
{
    assert(e.get_sort().is_bool());

    /* if (e.is_app())
    {
        func_decl dec = e.decl();

        if (dec.decl_kind() == Z3_OP_AND || dec.decl_kind() == Z3_OP_OR)
        {
            int numArgs = e.num_args();

            Z3_ast arguments [numArgs];
            for (int i = 0; i < numArgs; i++)
            {
                arguments[i] = (Z3_ast)negate(e.arg(i));
            }

            std::cout << e << std::endl;
            if (dec.decl_kind() == Z3_OP_AND)
            {
                return dec()
                //return to_expr(*context, Z3_mk_or(*context, numArgs, arguments));
            }
            else
            {
                //return to_expr(*context, Z3_mk_and(*context, numArgs, arguments));
            }
        }
    } */
    if (e.is_quantifier())
    {
        Z3_ast ast = (Z3_ast)e;

        int numBound = Z3_get_quantifier_num_bound(*context, ast);

        Z3_sort sorts [numBound];
        Z3_symbol decl_names [numBound];
        for (int i = 0; i < numBound; i++)
        {
            sorts[i] = Z3_get_quantifier_bound_sort(*context, ast, i);
            decl_names[i] = Z3_get_quantifier_bound_name(*context, ast, i);
        }

        Z3_ast quantAst = Z3_mk_quantifier(
                    *context,
                    !Z3_is_quantifier_forall(*context, ast),
                    Z3_get_quantifier_weight(*context, ast),
                    0,
                    {},
                    numBound,
                    sorts,
                    decl_names,
                    (Z3_ast)negate(e.body()));
        return to_expr(*context, quantAst);
    }

    return !e;
}

bool ExprSimplifier::isRelevant(const expr &e, int boundVariables, int currentDepth)
{
    if (e.is_var())
    {
        Z3_ast ast = (Z3_ast)e;
        int deBruijnIndex = Z3_get_index_value(*context, ast);

        return (deBruijnIndex - currentDepth) < boundVariables;
    }
    else if (e.is_app())
    {
        int numArgs = e.num_args();

        for (int i = 0; i < numArgs; i++)
        {
            bool relevant = isRelevant(e.arg(i), boundVariables, currentDepth);
            if (relevant)
            {
                return true;
            }
        }

        return false;
    }
    else if (e.is_quantifier())
    {
        Z3_ast ast = (Z3_ast)e;

        int numBound = Z3_get_quantifier_num_bound(*context, ast);

        return isRelevant(e.body(), boundVariables, currentDepth + numBound);
    }
    else
    {
        return false;
    }
}
