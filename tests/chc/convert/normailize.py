import re


def normalize(expr, mapping):
    """
    Replace each $f... identifier in expr with a sequential number.
    First occurrence of a given identifier gets 1, next new one gets 2, etc.
    """
    pattern = r"\$[f]?\d+"  # matches $f followed by digits
    counter = 0  # next number to assign

    def replace(match):
        nonlocal counter
        ident = match.group(0)  # e.g., '$f46908'
        return "$" + mapping[ident]

    return re.sub(pattern, replace, expr)


def deduceOrder(expr):
    slots = (
        expr.replace(")", "")
        .replace("(", "")
        .replace("\n", "")
        .replace(" ", "")
        .split(",")
    )
    order = {}
    for s in slots:
        order[s] = str(len(order))
    return order


# Example usage:
if __name__ == "__main__":
    order = """($f138633, $f138634, $f138635, $f138636, $f138637, $f138638, $f138639, $f138640, $f138641, $f138642, $f138643, $f138644, 
$f138645, $f138646, $f138647, $f138648, $f138649, $f138650, $f138651, $f138652, $f138653, $f138654)"""
    mapping = deduceOrder(order)

    expression = """(and <(eq (intType $f138640) (intType $f138639)) (eq (intType $f138640) (intType $f138639)) (leq (intType $f138633) (0)) (eq (nodeType $f138649) (binode (intType $f138651) (nodeType $f138652) (nodeType $f138653))) (eq (nodeType $f138646) (binode (intType $f138647) (nodeType $f138648) (nodeType $f138649))) (eq (nodeType $f138636) (binode (intType $f138639) (nodeType $f138637) (nodeType $f138638))) (eq (nodeType $f138636) (binode (intType $f138640) (nodeType $f138641) (nodeType $f138642))) (eq (nodeType $f138635) (binode (intType $f138639) (nodeType $f138637) (nodeType $f138638))) (eq (nodeType $f138635) (binode (intType $f138640) (nodeType $f138641) (nodeType $f138642))) (eq (intType $f138645) (add (intType $f138650) (1))) (eq (intType $f138634) (add (intType $f138643) (1))) (eq (intType $f138644) (add (intType $f138654) (1))) (eq (nodeType $f138636) (nodeType $f138635)) (eq (nodeType $f138637) (nodeType $f138641)) (eq (nodeType $f138635) (nodeType $f138636)) (eq (nodeType $f138638) (nodeType $f138642)) (eq (binode (intType $f138639) (nodeType $f138637) (nodeType $f138638)) (binode (intType $f138640) (nodeType $f138641) (nodeType $f138642)))>)"""
    normalized = normalize(expression, mapping)
    print(normalized)
