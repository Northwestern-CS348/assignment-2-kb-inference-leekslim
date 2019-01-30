import read, copy
from util import *
from logical_classes import *

verbose = 0

class KnowledgeBase(object):
    def __init__(self, facts=[], rules=[]):
        self.facts = facts
        self.rules = rules
        self.ie = InferenceEngine()

    def __repr__(self):
        return 'KnowledgeBase({!r}, {!r})'.format(self.facts, self.rules)

    def __str__(self):
        string = "Knowledge Base: \n"
        string += "\n".join((str(fact) for fact in self.facts)) + "\n"
        string += "\n".join((str(rule) for rule in self.rules))
        return string

    def _get_fact(self, fact):
        """INTERNAL USE ONLY
        Get the fact in the KB that is the same as the fact argument

        Args:
            fact (Fact): Fact we're searching for

        Returns:
            Fact: matching fact
        """
        for kbfact in self.facts:
            if fact == kbfact:
                return kbfact

    def _get_rule(self, rule):
        """INTERNAL USE ONLY
        Get the rule in the KB that is the same as the rule argument

        Args:
            rule (Rule): Rule we're searching for

        Returns:
            Rule: matching rule
        """
        for kbrule in self.rules:
            if rule == kbrule:
                return kbrule

    def kb_add(self, fact_rule):
        """Add a fact or rule to the KB
        Args:
            fact_rule (Fact|Rule) - the fact or rule to be added
        Returns:
            None
        """
        printv("Adding {!r}", 1, verbose, [fact_rule])
        if isinstance(fact_rule, Fact):  # if adding a fact...
            if fact_rule not in self.facts:  # check if already in kb
                self.facts.append(fact_rule)
                for rule in self.rules:
                    self.ie.fc_infer(fact_rule, rule, self)
            else:
                if fact_rule.supported_by:  # if already in kb, see if supported by something, i.e. it was inferred
                    ind = self.facts.index(fact_rule)  # find the fact in kb
                    for f in fact_rule.supported_by:  # for everything that led to inference...
                        self.facts[ind].supported_by.append(f)  # add the new support for the fact
                else:
                    ind = self.facts.index(fact_rule)  # otherwise, it must be an assertion for
                    self.facts[ind].asserted = True  # something that has already been inferred
        elif isinstance(fact_rule, Rule):  # otherwise if it is a rule
            if fact_rule not in self.rules:
                self.rules.append(fact_rule)  # add to kb if not already
                for fact in self.facts:
                    self.ie.fc_infer(fact, fact_rule, self)  # iterate over facts to infer new things
            else:
                if fact_rule.supported_by:
                    ind = self.rules.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.rules[ind].supported_by.append(f)
                else:
                    ind = self.rules.index(fact_rule)
                    self.rules[ind].asserted = True

    def kb_assert(self, fact_rule):
        """Assert a fact or rule into the KB

        Args:
            fact_rule (Fact or Rule): Fact or Rule we're asserting
        """
        printv("Asserting {!r}", 0, verbose, [fact_rule])
        self.kb_add(fact_rule)

    def kb_ask(self, fact):
        """Ask if a fact is in the KB

        Args:
            fact (Fact) - Statement to be asked (will be converted into a Fact)

        Returns:
            listof Bindings|False - list of Bindings if result found, False otherwise
        """
        print("Asking {!r}".format(fact))
        if factq(fact):
            f = Fact(fact.statement)
            bindings_lst = ListOfBindings()
            # ask matched facts
            for fact in self.facts:
                binding = match(f.statement, fact.statement)
                if binding:
                    bindings_lst.add_bindings(binding, [fact])

            return bindings_lst if bindings_lst.list_of_bindings else []

        else:
            print("Invalid ask:", fact.statement)
            return []

    def kb_retract(self, fact_or_rule):
        """Retract a fact from the KB

        Args:
            fact (Fact) - Fact to be retracted

        Returns:
            None
        """
        printv("Retracting {!r}", 0, verbose, [fact_or_rule])
        ####################################################
        # Student code goes here
        if isinstance(fact_or_rule, Fact):  # first see if it is a rule or fact
            fact_in_kb = None  # get fact object in kb that has complete attributes
            for f in self.facts:
                if f == fact_or_rule:
                    fact_in_kb = f
            if not fact_in_kb:  # fact was not found in kb list
                print("fact was not found in kb")  # should not happen, but in case fact not in kb
            elif fact_in_kb.supported_by:  # if retracting assertion but still supported
                fact_in_kb.asserted = False
            else:  # retracting a fact that is not supported by assertion or inference
                for supported_fact in fact_in_kb.supports_facts:  # for every fact it supports
                    for pair in supported_fact.supported_by:  # find all pairs that contain this retracting fact
                        if fact_in_kb in pair:  # retracting fact may support the same fact in multiple ways
                            supported_fact.supported_by.remove(pair)  # all fact-rule pairs that must be rescinded
                            pair[1].supports_facts.remove(supported_fact)  # remove the supported fact from the rule as well
                    if (not supported_fact.supported_by) and (not supported_fact.asserted):  # if no longer supported or asserted
                        self.kb_retract(supported_fact)  # recurse onto this fact; if fact still supported, step is done
                for supported_rule in fact_in_kb.supports_rules:  # for every rule it supports
                    for pair in supported_rule.supported_by:
                        if fact_in_kb in pair:
                            supported_rule.supported_by.remove(pair)
                            pair[1].supports_rules.remove(supported_rule)
                    if (not supported_rule.supported_by) and (not supported_rule.asserted):  # same as above
                        self.kb_retract(supported_rule)
                self.facts.remove(fact_in_kb)
        elif isinstance(fact_or_rule, Rule):
            rule_in_kb = None
            for r in self.rules:
                    if r == fact_or_rule:
                        rule_in_kb = r
            if not rule_in_kb:
                print("rule was not found in kb")  # same as above
            elif rule_in_kb.asserted:
                print('cannot retract asserted rules')
            elif rule_in_kb.supported_by:  # rule is still supported by other inferences, ignore
                print('rule is still supported, this should not be retracted')
            else:  # assuming supported by and support directly reference each other in kb as above
                for sf in rule_in_kb.supports_facts:  # sf is supported_fact as above
                    for pair in sf.supported_by:
                        if rule_in_kb in pair:
                            sf.supported_by.remove(pair)
                            pair[0].supports_facts.remove(sf)
                    if (not sf.supported_by) and (not sf.asserted):
                        self.kb_retract(sf)  # no longer has any supports, so for sure retractable
                for sr in rule_in_kb.supports_rules:
                    for pair in sr.supported_by:
                        if rule_in_kb in pair:
                            sr.supported_by.remove(pair)
                            pair[0].supports_rules.remove(sr)
                    if (not sr.supported_by) and (not sr.asserted):
                        self.kb_retract(sr)
                self.rules.remove(rule_in_kb)
        else:
            print("unsupported, not fact or rule")


class InferenceEngine(object):
    def fc_infer(self, fact, rule, kb):
        """Forward-chaining to infer new facts and rules

        Args:
            fact (Fact) - A fact from the KnowledgeBase
            rule (Rule) - A rule from the KnowledgeBase
            kb (KnowledgeBase) - A KnowledgeBase

        Returns:
            Nothing            
        """
        printv('Attempting to infer from {!r} and {!r} => {!r}', 1, verbose,
            [fact.statement, rule.lhs, rule.rhs])
        ####################################################
        # Student code goes here
        left_most = rule.lhs[0]  # get left most statement in lhs of rule
        binding = match(fact.statement, left_most)  # Check if fact statement matches LHS statement in rule
        if binding:  # if there is a match, check to see if there are more statements in the lhs
            pair = (fact, rule)  # generate fact rule pair, all supported by is a fact rule pair
            if len(rule.lhs) > 1:
                new_lhs = []  # generate empty list for lhs
                for ls in rule.lhs[1:]:  # for every left statement in lhs
                    new_lhs.append(instantiate(ls, binding))  # add new inferred rule's statements to lhs
                new_rhs = instantiate(rule.rhs, binding)
                new_rule = Rule([new_lhs, new_rhs], [pair])
                kb.kb_assert(new_rule)
                fact.supports_rules.append(new_rule)  # add to matching rule and fact's supports rules
                rule.supports_rules.append(new_rule)
            else:  # assert new fact, assuming rhs can only contain one statement
                new_fact = Fact(instantiate(rule.rhs, binding), [pair])
                kb.kb_assert(new_fact)
                fact.supports_facts.append(new_fact)
                rule.supports_facts.append(new_fact)
