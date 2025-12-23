from collections import defaultdict, Counter
from typing import List, Tuple, Dict
import itertools


def canonical_form(term_list: List[Tuple]) -> str:
    """
    Convert a list of function calls to a canonical string representation
    that is invariant under variable renaming and list permutation.

    Steps:
    1. Extract all variables and assign them canonical IDs based on their
       "fingerprint" in the multiset
    2. Rewrite all terms using these canonical IDs
    3. Sort the rewritten terms lexicographically
    4. Return as a string

    Args:
        term_list: List of tuples like ('f', 'x', 'y') for f(x, y)

    Returns:
        Canonical string representation
    """
    if not term_list:
        return ""

    # Step 1: Build variable connectivity graph
    var_occurrences = defaultdict(list)
    var_adjacency = defaultdict(Counter)

    for idx, (func_name, *args) in enumerate(term_list):
        # Record occurrence context for each variable
        for i, var in enumerate(args):
            var_occurrences[var].append((func_name, i, tuple(sorted(args))))

        # Build adjacency between variables in same term
        for i in range(len(args)):
            for j in range(i + 1, len(args)):
                var_adjacency[args[i]][args[j]] += 1
                var_adjacency[args[j]][args[i]] += 1

    print("term_list", term_list)
    print("var_occurrences", var_occurrences)
    print("var_adjacency", var_adjacency)

    # Step 2: Compute fingerprints for each variable
    # A fingerprint captures how a variable is used in the entire list
    fingerprints = {}
    for var in var_occurrences:
        # Sort occurrences to get canonical order
        occ_list = sorted(var_occurrences[var])

        # Build adjacency fingerprint
        adj_fingerprint = []
        for other_var, count in sorted(var_adjacency[var].items()):
            # For the other variable, we need to normalize
            adj_fingerprint.append((other_var, count))

        # Create fingerprint tuple
        fingerprint = (
            tuple(occ_list),  # How this variable is used
            tuple(adj_fingerprint),  # What it co-occurs with
        )
        fingerprints[var] = fingerprint
    print("fingerprints", fingerprints)

    # Step 3: Group variables by their fingerprint
    # Variables with identical fingerprints are indistinguishable
    fingerprint_to_vars = defaultdict(list)
    for var, fingerprint in fingerprints.items():
        # Convert to hashable tuple
        # We need to flatten the adjacency part since it references other vars
        # Instead, compute a stable representation
        occ_repr = tuple(sorted(str(occ) for occ in var_occurrences[var]))
        adj_repr = tuple(
            sorted((count,) for other_var, count in var_adjacency[var].items())
        )
        stable_fingerprint = (occ_repr, adj_repr)
        fingerprint_to_vars[stable_fingerprint].append(var)

    # Step 4: Assign canonical IDs to variables
    # Sort fingerprint groups to get deterministic ordering
    canonical_id = 0
    var_to_canonical = {}

    for fingerprint in sorted(fingerprint_to_vars.keys()):
        for var in sorted(fingerprint_to_vars[fingerprint]):
            var_to_canonical[var] = f"v{canonical_id}"
            canonical_id += 1

    # Step 5: Rewrite all terms with canonical IDs
    rewritten_terms = []
    for func_name, *args in term_list:
        canonical_args = tuple(var_to_canonical[arg] for arg in args)
        # Create a tuple representation that sorts well
        term_repr = (func_name, *canonical_args)
        rewritten_terms.append(term_repr)

    # Step 6: Sort terms lexicographically
    sorted_terms = sorted(rewritten_terms)

    # Step 7: Convert to canonical string
    return "|".join(str(term) for term in sorted_terms)


def are_canonically_equivalent(list1: List[Tuple], list2: List[Tuple]) -> bool:
    """
    Check if two lists are equivalent using canonical forms.
    """
    return canonical_form(list1) == canonical_form(list2)


# Even Simpler Approach using graph-based canonical labeling
def graph_based_canonical_form(term_list: List[Tuple]) -> str:
    """
    Alternative approach: Treat as a bipartite graph and compute canonical labeling.
    """
    from collections import defaultdict

    # Create a graph representation
    # Nodes: variables + terms (with function names as node labels)
    # Edges: from term nodes to variable nodes with position labels

    # We'll create a string representation that's canonical

    # Step 1: Map each unique term pattern to a canonical form
    term_patterns = {}
    for func_name, *args in term_list:
        # Create pattern: function_name + sorted argument positions
        # But we need to account for repeated variables
        pattern = [func_name]
        var_positions = {}
        normalized_args = []
        next_id = 0

        for arg in args:
            if arg not in var_positions:
                var_positions[arg] = next_id
                next_id += 1
            normalized_args.append(var_positions[arg])

        # Add arity and pattern
        pattern.append(len(args))
        pattern.extend(normalized_args)
        term_pattern = tuple(pattern)

        term_patterns.setdefault(term_pattern, 0)
        term_patterns[term_pattern] += 1

    # Step 2: Sort patterns by their structure, then by count
    sorted_patterns = []
    for pattern, count in sorted(term_patterns.items()):
        sorted_patterns.append(f"{pattern}:{count}")

    return ";".join(sorted_patterns)


def advanced_canonical_form(term_list: List[Tuple]) -> str:
    """
    More advanced canonical form that handles complex cases.

    Approach:
    1. Build a graph of variable connections
    2. Compute connected components
    3. Within each component, compute canonical labeling
    4. Sort components and terms
    """
    from collections import defaultdict, deque

    # Build adjacency between variables
    adjacency = defaultdict(set)
    term_info = []  # Store (func_name, args_list, normalized_args)

    # First pass: build variable connectivity
    for func_name, *args in term_list:
        term_vars = list(args)
        term_info.append((func_name, term_vars))

        # Connect all variables in this term
        for i in range(len(term_vars)):
            for j in range(i + 1, len(term_vars)):
                var1, var2 = term_vars[i], term_vars[j]
                adjacency[var1].add(var2)
                adjacency[var2].add(var1)

    # Find connected components of variables
    visited = set()
    components = []

    for var in list(adjacency.keys()):
        if var not in visited:
            # BFS to find component
            component = []
            queue = deque([var])
            visited.add(var)

            while queue:
                current = queue.popleft()
                component.append(current)

                for neighbor in adjacency[current]:
                    if neighbor not in visited:
                        visited.add(neighbor)
                        queue.append(neighbor)

            components.append(component)

    # For each component, create a canonical representation
    component_signatures = []

    for component in components:
        # Get all terms involving variables in this component
        component_terms = []
        for func_name, args in term_info:
            if any(arg in component for arg in args):
                # Remap variables within component to canonical names
                var_mapping = {}
                next_id = 0
                mapped_args = []

                for arg in args:
                    if arg in component:
                        if arg not in var_mapping:
                            var_mapping[arg] = f"v{next_id}"
                            next_id += 1
                        mapped_args.append(var_mapping[arg])
                    else:
                        # Variable from another component
                        mapped_args.append(f"ext_{arg}")

                component_terms.append((func_name, tuple(mapped_args)))

        # Sort terms and create signature for this component
        sorted_terms = sorted(set(component_terms))  # Use set to deduplicate
        term_counts = Counter(component_terms)
        component_sig = []

        for term in sorted_terms:
            component_sig.append(f"{term}*{term_counts[term]}")

        component_signatures.append(";".join(component_sig))

    # Sort component signatures and combine
    return "|".join(sorted(component_signatures))


# Test the canonical form approach
def test_canonical_forms():
    test_cases = [
        # Case 1: Simple renaming
        ([("f", "x", "y")], [("f", "z", "w")]),
        # Case 2: Symmetric function
        ([("f", "x", "y"), ("f", "y", "x")], [("f", "y", "z"), ("f", "z", "y")]),
        (
            [("f", "x", "y"), ("f", "y", "x"), ("g", "x", "y")],
            [("f", "y", "x"), ("f", "x", "y"), ("g", "x", "y")],
        ),
        ([("f", "x", "y"), ("f", "x", "x")], [("f", "a", "b"), ("f", "a", "a")]),
        # Case 5: Complex pattern with multiple variables
        (
            [("f", "x", "y"), ("g", "y", "z"), ("h", "z", "x")],
            [("g", "b", "c"), ("f", "a", "b"), ("h", "c", "a")],
        ),
        # Case 6: Empty lists
        ([], []),
        ([("f", "x", "y")], [("f", "x", "x")]),
        (
            [
                ("p", "n", "k", "m"),
                ("a", "u"),
                ("a", "t"),
                ("ml", "t", "k"),
                ("ml", "u", "m"),
            ],
            [
                ("p", "n", "k", "m"),
                ("a", "t"),
                ("a", "u"),
                ("ml", "t", "k"),
                ("ml", "u", "m"),
            ],
        ),
        ([("f", "x", "y"), ("f", "z", "z")], [("f", "x", "y"), ("f", "x", "x")]),
    ]

    print("Testing canonical forms:")
    print("-" * 50)

    for i, (list1, list2) in enumerate(test_cases):
        cf1 = canonical_form(list1)
        cf2 = canonical_form(list2)

        adv_cf1 = advanced_canonical_form(list1)
        adv_cf2 = advanced_canonical_form(list2)

        print(f"\nTest case {i+1}:")
        print(f"  List1: {list1}")
        print(f"  List2: {list2}")
        print(f"  Standard canonical form equality: {cf1 == cf2}")
        print(f"  Advanced canonical form equality: {adv_cf1 == adv_cf2}")

        print(f"\n  Standard CF1: {cf1}")
        print(f"  Standard CF2: {cf2}")


def random_test_canonical_forms():

    test_cases = []

    print("Testing canonical forms:")
    print("-" * 50)

    for i, (list1, list2) in enumerate(test_cases):
        cf1 = canonical_form(list1)
        cf2 = canonical_form(list2)

        adv_cf1 = advanced_canonical_form(list1)
        adv_cf2 = advanced_canonical_form(list2)

        print(f"\nTest case {i+1}:")
        print(f"  List1: {list1}")
        print(f"  List2: {list2}")
        print(f"  Standard canonical form equality: {cf1 == cf2}")
        print(f"  Advanced canonical form equality: {adv_cf1 == adv_cf2}")

        print(f"\n  Standard CF1: {cf1}")
        print(f"  Standard CF2: {cf2}")


if __name__ == "__main__":
    test_canonical_forms()
