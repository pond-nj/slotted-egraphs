import itertools

# Define the fixed parts
variables = ["x", "y", "z"]
perms_f = list(itertools.permutations(variables))
g_original = ["y", "x", "z"]
g_swapped = ["y", "z", "x"]
g_versions = [g_original, g_swapped]
h_fixed = ("h", ["w"])
count = 0

# Generate all combinations
for perm in perms_f:
    for g_ver in g_versions:
        current_list = [("f", list(perm)), h_fixed, ("g", g_ver)]

        # Compute canonical renaming
        var_to_num = {}
        next_num = 0
        canon_funcs = []

        current_list_str_list = []
        for name, args in current_list:
            canon_args = []
            for var in args:
                if var not in var_to_num:
                    var_to_num[var] = next_num
                    next_num += 1
                canon_args.append(str(var_to_num[var]))
            canon_funcs.append(name + "(" + ",".join(canon_args) + ")")
            current_list_str_list.append(name + "(" + ",".join(args) + ")")

        canon_str = ", ".join(canon_funcs)
        print(f"{count+ 1})", ", ".join(current_list_str_list), "=", canon_str)
        count += 1
