/*
  To compile:
    $> g++ -std=c++11 -O2 exhaust_proof.cpp -o exhaust_proof

  To run proof of first lemma, use:
    $> echo "1" | ./exhaust_proof

  To run proof of second lemma, use:
    $> echo "2" | ./exhaust_proof

  In both cases, the output contains the conclusion:
    "Guaranteed edge in formula graph: 3->1 = 5->1"
*/
#include <bits/stdc++.h>

using namespace std;

using Matrix = vector<string>;

vector<Matrix> GenMatricesFromPattern(const Matrix &pattern) {
  const int N = pattern.size();
  assert(N > 0);
  const int M = pattern[0].size();
  vector<pair<int, int>> empty_pos;
  for (int i = 0; i < N; ++i) {
    for (int j = 0; j < M; ++j) {
      if (pattern[i][j] == '?') {
        empty_pos.emplace_back(i, j);
      }
    }
  }
  vector<Matrix> matrices;
  Matrix mat = pattern;
  for (int mask = 0; mask < (1 << empty_pos.size()); ++mask) {
    for (int index = 0; index < empty_pos.size(); ++index) {
      if (mask & (1 << index)) {
        mat[empty_pos[index].first][empty_pos[index].second] = '1';
      } else {
        mat[empty_pos[index].first][empty_pos[index].second] = '0';
      }
    }
    matrices.push_back(mat);
  }
  return matrices;
}

// Union-Find data structure.
struct UF {
  vector<int> e, normalized;
  void normalizeNontrivial() {
    int index = 0;
    for (int i = 0; i < e.size(); ++i)
      if (size(i) > 1) {
        if (normalized[find(i)] == -1) {
          normalized[find(i)] = index++;
        }
        normalized[i] = normalized[find(i)];
      }
  }
  UF(int n) : e(n, -1), normalized(n, -1) {}
  bool sameSet(int a, int b) { return find(a) == find(b); }
  int size(int x) { return -e[find(x)]; }
  int find(int x) { return e[x] < 0 ? x : e[x] = find(e[x]); }
  bool join(int a, int b) {
    a = find(a), b = find(b);
    if (a == b)
      return false;
    if (e[a] > e[b])
      swap(a, b);
    e[a] += e[b];
    e[b] = a;
    return true;
  }
};

struct Edge {
  int from, to;
  Edge() = default;
  Edge(int from_, int to_) : from(from_), to(to_) {}
  friend bool operator==(const Edge &e1, const Edge &e2) {
    return make_pair(e1.from, e1.to) == make_pair(e2.from, e2.to);
  }
  friend bool operator<(const Edge &e1, const Edge &e2) {
    return make_pair(e1.from, e1.to) < make_pair(e2.from, e2.to);
  }
};

pair<Edge, Edge> NormalizeEquality(pair<Edge, Edge> eq) {
  if (eq.first.from == eq.second.from) {
    swap(eq.first.from, eq.first.to);
    swap(eq.second.from, eq.second.to);
  }
  assert(eq.first.to == eq.second.to);
  assert(eq.first.from != eq.second.from);
  if (eq.first.from > eq.second.from) {
    swap(eq.first, eq.second);
  }
  return eq;
}

// The Colorful Graph.
struct ComponentsGraph {
  int M;
  set<pair<Edge, Edge>> equalities;
  vector<vector<Edge>> edges_for_color;
  map<pair<int, int>, int> color_of_edge;
  ComponentsGraph() = default;
  ComponentsGraph(int M_, set<pair<Edge, Edge>> &&equalities_,
                  vector<vector<Edge>> &&edges_for_color_)
      : M(M_), equalities(equalities_), edges_for_color(edges_for_color_) {
    for (int i = 0; i < edges_for_color.size(); ++i) {
      for (const Edge &e : edges_for_color[i]) {
        color_of_edge[make_pair(e.from, e.to)] =
            color_of_edge[make_pair(e.to, e.from)] = i;
      }
    }
  }

  static ComponentsGraph
  NoComponentsGraph(set<pair<Edge, Edge>> &&equalities_) {
    return ComponentsGraph(-1, move(equalities_), {});
  }

  bool IsNoComponentsGraph() const { return M == -1; }
};

ComponentsGraph BuildComponentsGraph(const Matrix &mat) {
  const int N = mat.size();
  assert(N > 0);
  const int M = mat[0].size();
  const int edges = M * (M - 1);
  vector<vector<int>> edge(M, vector<int>(M, -1));
  for (int i = 0, index = 0; i < M; ++i) {
    for (int j = i + 1; j < M; ++j) {
      edge[i][j] = index++;
      edge[j][i] = index++;
    }
  }
  UF union_find(edges);
  set<pair<Edge, Edge>> equalities;
  for (int i = 0; i < M; ++i) {
    for (int j = 0; j < M; ++j) {
      for (int k = i + 1; k < M; ++k) {
        if (i != j && j != k) {
          for (int a = 0; a < N; ++a) {
            for (int b = a + 1; b < N; ++b) {
              const char val0 = mat[a][i];
              const char val1 = '0' ^ '1' ^ val0;
              if (mat[a][i] == val0 && mat[a][j] == val1 && mat[a][k] == val0 &&
                  mat[b][i] == val1 && mat[b][j] == val0 && mat[b][k] == val1) {
                union_find.join(edge[i][j], edge[k][j]);
                union_find.join(edge[j][i], edge[j][k]);
                equalities.insert(
                    NormalizeEquality(make_pair(Edge(i, j), Edge(k, j))));
              }
            }
          }
        }
      }
    }
  }
  // Find if a clear contradiction exists; i.e. complementary
  // edges in the same connected component.
  for (int i = 0; i < M; ++i) {
    for (int j = i + 1; j < M; ++j) {
      if (union_find.sameSet(edge[i][j], edge[j][i])) {
        return ComponentsGraph::NoComponentsGraph(move(equalities));
      }
    }
  }
  // Normalize components of size > 1.
  vector<vector<int>> color(M, vector<int>(M, -1));
  union_find.normalizeNontrivial();
  int max_color = -2;
  for (int i = 0; i < M; ++i) {
    for (int j = 0; j < M; ++j) {
      if (i != j && union_find.size(edge[i][j]) > 1) {
        color[i][j] = union_find.normalized[edge[i][j]];
        max_color = max(max_color, color[i][j]);
      }
    }
  }
  // Now renormalize to eliminate opposite edges from counting.
  vector<int> renormalized(max(0, max_color), -1);
  int new_colors = 0;
  for (int i = 0; i < M; ++i) {
    for (int j = i + 1; j < M; ++j) {
      if (color[i][j] >= 0) { // Edge is not singleton.
        if (renormalized[color[i][j]] == -1) {
          renormalized[color[i][j]] = new_colors++;
          renormalized[color[j][i]] = -2;
        }
      }
    }
  }
  assert(new_colors - 1 == max_color / 2);
  for (int i = 0; i < M; ++i) {
    for (int j = 0; j < M; ++j) {
      if (i != j && color[i][j] >= 0) { // Edge is not singleton.
        color[i][j] = renormalized[color[i][j]];
      }
    }
  }
  vector<vector<Edge>> edges_for_color(new_colors);
  for (int i = 0; i < M; ++i) {
    for (int j = 0; j < M; ++j) {
      if (i != j && color[i][j] >= 0) {
        assert(color[i][j] < new_colors);
        edges_for_color[color[i][j]].emplace_back(i, j);
      }
    }
  }
  return ComponentsGraph(M, move(equalities), move(edges_for_color));
}

void ProveTheTwoLemmas(int lemma) {
  assert(lemma == 1 or lemma == 2);
  vector<Matrix> matrices;
  if (lemma == 1) {
    matrices = GenMatricesFromPattern({
        "01?1?", //
        "10?0?", //
        "?01?1", //
        "?10?0", //
    });
  } else {
    matrices = GenMatricesFromPattern({
        "01?0?", //
        "10?1?", //
        "?01?1", //
        "?10?0", //
    });
  }

  set<pair<Edge, Edge>> common_eq; // Edges found in all formula graphs.
  bool first_time = true;
  int found_matrices = 0;
  for (const auto &mat : matrices) {
    // Build colorful graph.
    const ComponentsGraph cg = BuildComponentsGraph(mat);
    // Colorful graph needs to exist.
    if (cg.IsNoComponentsGraph())
      continue;
    // Conditions in both lemmas, note -1 everywhere since code works 0-indexed.
    if (cg.equalities.count(NormalizeEquality({Edge{0, 1}, Edge{2, 1}})))
      continue;
    if (cg.equalities.count(NormalizeEquality({Edge{0, 1}, Edge{4, 1}})))
      continue;

    cerr << "Found abiding matrix #" << ++found_matrices << endl;
    if (first_time) {
      first_time = false;
      common_eq = cg.equalities;
    } else {
      set<pair<Edge, Edge>> inters;
      set_intersection(common_eq.begin(), common_eq.end(),
                       cg.equalities.begin(), cg.equalities.end(),
                       inserter(inters, inters.begin()));
      common_eq = inters;
    }
  }
  for (const pair<Edge, Edge> &eq : common_eq) {
    // +1 everywhere because code works 0-indexed.
    cout << "Guaranteed edge in formula graph: " << eq.first.from + 1 << "->"
         << eq.first.to + 1 << " = " << eq.second.from + 1 << "->"
         << eq.second.to + 1 << endl;
  }
}

int main() {
  int lemma;
  cin >> lemma;
  ProveTheTwoLemmas(lemma);
}