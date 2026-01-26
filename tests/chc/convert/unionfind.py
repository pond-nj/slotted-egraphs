class UnionFind:
    def __init__(
        self,
    ):
        self.parent = []

    def extend(self):
        self.parent.append(len(self.parent))

    def find(self, i):
        if self.parent[i] == i:
            return i
        # Path compression: make every node on the path point directly to the root
        self.parent[i] = self.find(self.parent[i])
        return self.parent[i]

    def union(self, i, j):
        root_i = self.find(i)
        root_j = self.find(j)

        if root_i != root_j:
            self.parent[root_j] = root_i
            return True
        return False

    def connected(self, i, j):
        return self.find(i) == self.find(j)
