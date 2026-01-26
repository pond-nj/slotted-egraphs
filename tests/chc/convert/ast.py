from dataclasses import dataclass
from enum import Enum
from typing import Union


class ConstrOP(Enum):
    eq = "="
    neq = "=\\="
    add = "+"
    minus = "-"
    leq = "=<"
    geq = ">="
    less = "<"
    greater = ">"
    emptyList = "[]"
    list = "list"
    binode = "node"


@dataclass
class Var:
    val: str | int

    def __str__(self):
        return f"{self.val}"


@dataclass
class Constr:
    Op: ConstrOP
    Args: list[Union["Constr", Var]]

    def __str__(self):
        return f"{self.Op.name}({', '.join([str(x) for x in self.Args])})"


@dataclass
class PredApp:
    PredName: str
    Args: list[Var]

    def len(self):
        return len(self.Args)

    def __iter__(self):
        return iter(self.Args)

    def __str__(self):
        return f"{self.PredName}({', '.join([str(x) for x in self.Args])})"


@dataclass
class CHC:
    Head: PredApp
    Constr: list[Constr]
    PredApps: list[PredApp]
    original: str

    def renameHead(self):
        count = 0

        def rename(x):
            nonlocal count
            count += 1
            return Var("new" + str(count - 1))

        newHead = PredApp(
            self.Head.PredName, list(map(lambda x: rename(x), self.Head.Args))
        )

        for i, v in enumerate(self.Head):
            self.Constr.append(
                Constr(
                    ConstrOP.eq,
                    [
                        v,
                        Var("new" + str(i)),
                    ],
                )
            )

        self.Head = newHead

    def __str__(self):
        return f"CHC({self.Head}, {self.Constr}, {self.PredApps})"
