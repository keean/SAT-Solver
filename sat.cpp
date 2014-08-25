#include <fstream>
#include <iostream>
#include <sstream>
#include <vector>
#include <algorithm>

#include "Parser-Combinators/profile.hpp"
#include "Parser-Combinators/parser_simple.hpp"

using namespace std;

//----------------------------------------------------------------------------
// CNF Parser

is_char const is_lower_c('c');
is_char const is_lower_p('p');
is_char const is_nl('\n');
is_char const is_eof(EOF);
is_either const is_nl_or_eof(is_nl, is_eof);
is_not const not_nl_or_eof(is_nl_or_eof);

struct format_error : public runtime_error {
    int const row;
    string const exp;
    format_error(string const& what, int row)
        : runtime_error(what), row(row) {}
};

struct cnf_parser : public parser {
    cnf_parser(istream &f) : parser(f) {}

    void comment() {
        while (accept(is_lower_c)) {
            string comment;
            while (accept(not_nl_or_eof, &comment));
            space();
        }
    }
        
    int operator() (vector<vector<int>>& R) {
        comment();

        if (accept(is_lower_p)) {
            space();
            string format;
            name(&format);
            if (format != "cnf") {
                throw format_error("format " + format + " not supported", get_row());
            }
            space();
            
            string var_str;
            number(&var_str);
            int var = stoi(var_str, nullptr);
            space();

            string cls_str;
            number(&cls_str);
            int cls = stoi(cls_str, nullptr);
            while (accept(not_nl_or_eof));

            //cout << "variables=" << var << " clauses=" << cls << "\n";

            R.resize(cls);
            for (int j = 0; j < cls; ++j) {
                int v;
                //cout << j << ": ";
                while (true) {
                    space();
                    string vstr;
                    signed_number(&vstr);
                    v = stoi(vstr, nullptr);
                    if (v == 0) {
                        break;
                    }
                    //cout << v << " ";
                    R[j].push_back(v);
                } 
                //cout << "\n";
            }

            return var;
        }

        return 0;
    }
};

//----------------------------------------------------------------------------
// Helper functions.

struct abs_descending {
    bool operator() (int const i, int const j) {
        return abs(i) < abs(j);
    }
} abs_descending;

struct lex_abs_desc {
    bool operator() (vector<int> const& u, vector<int> const& v) {
        auto const l1 = u.end();
        auto const l2 = v.end();
        auto f1 = u.begin();
        auto f2 = v.begin();
        while (f1 != l1) {
            auto const x = abs(*f1);
            auto const y = abs(*f2);
            if ((f2 == l2) || x > y) {
                return false;
            } else if (x < y) {
                return true;
            } 
            ++f1; ++f2;
        }
        return f2 != l2;
    }
} lex_abs_desc;

template <typename T> int sum_sizes(vector<vector<T>> const& v) {
    int s {};
    for (int j = 0; j < v.size(); ++j) {
        s += v[j].size();
    };
    return s;
}

bool verify(vector<vector<int>> const& cnf, int x[]) {
    bool s = true;

    for (int j = 0; j < cnf.size(); ++j) {
        bool c = false;
        for (int i = 0; i < cnf[j].size(); ++i) {
            int l = cnf[j][i];
            if (l < 0) {
                if ((x[-l] & 1) == 0) {
                    c = true;
                    break;
                }
            } else {
                if ((x[l] & 1) == 1) {
                    c = true;
                    break;
                }
            }
        }
        if (c == false) {
            s = false;
            break;
        }
    }

    return s;
}

//----------------------------------------------------------------------------
// SAT Algorithm A

typedef struct {} sata;

bool sat_a(int const n, vector<vector<int>> const& R) {
    int const m = R.size();
    int const m2 = sum_sizes(R);

    int s = (n << 1) + 2;
    int e = s + m2;
    int L[e];
    int F[e];
    int B[e];
    int C[e];
    int START[m + 1];
    int SIZE[m + 1];
    int p = 0;

    for (;p < 2; ++p) {
        L[p] = 0;
        F[p] = 0;
        B[p] = 0;
        C[p] = 0;
    }

    for (;p < s; ++p) {
        L[p] = 0;
        F[p] = p;
        B[p] = p;
        C[p] = 0;
    }

    p = e - 1;

    for (int j = 0; j < R.size(); ++j) {
        vector<int> S = R[j];
        sort(S.begin(), S.end(), abs_descending);

        for (int i = 0; i < S.size(); ++i) {

            int l = S[i] << 1;

            if (l < 0) {
                l = (-l)^1;
            }

            int const b = B[l];
            int const f = F[b];

            L[p] = l;
            F[p] = f;
            B[p] = b;
            C[p] = j + 1;


            B[l] = p;
            F[b] = p;
            ++C[l];
            --p;
        }
        START[j + 1] = p + 1;
        SIZE[j + 1] = S.size();
    }

A1: // Initialise
    profile<sata> prof;
    int const n2 = (n << 1) + 2;
    int M[n + 1];
    int a = m;
    int d = 1;
    int l;
    int x = 0;

A2: // Choose
    l = d + d;
    if (C[l] <= C[l+1]) {
        ++l;
    }
    M[d] = (l & 1) + ((C[l^1] == 0) << 2);
    if (x > 10000000) {
        cout << d << ": ";
        for (int i = 1; i <= d; ++i) {
            cout << M[i];
        }
        cout << "\n";
        x = 0;
    } else {
        ++x;
    }
    if (C[l] == a) {
        int X[n + 1];
        for (int j = 1; j <= d; ++j) {
            X[j] = 1 ^ (M[j] & 1);
            cout << X[j];
        }
        if (verify(R, X)) {
            cout << " VERIFIED";
        }
        return true;;
    }

A3: // Remove l
    int c = F[l^1];
    while (c >= n2) {
        int const j = C[c];
        int const i = SIZE[j];
        if (i > 1) {
            SIZE[j] = i - 1;
            c = F[c];
        } else if (i == 1) {
            c = B[c];
            while (c >= n2) {
                int const j = C[c];
                int const i = SIZE[j];
                SIZE[j] = i + 1;
                c = B[c];
            }
            goto A5;
        }
    }

A4: // Deactivate clauses of l
    c = F[l];
    while (c >= n2) {
        int const j = C[c];
        int const i = START[j];
        c = F[c];
        for (int p = i; p < i + SIZE[j] - 1; ++p) {
            int const q = F[p];
            int const r = B[p];
            B[q] = r;
            F[r] = q;
            --C[L[p]];
        }
    }
    a -= C[l];
    ++d;
    goto A2;

A5: // Try again
    if (M[d] < 2) {
        M[d] = 3 - M[d];
        l = (d << 1) + (M[d] & 1);
        goto A3;
    }

A6: // Backtrack
    if (d == 1) {
        return false;
    }
    --d;
    l = (d << 1) + (M[d] & 1);

A7: // Reactivate clauses of l
    a += C[l];
    c = B[l];
    while (c >= n2) {
        int const j = C[c];
        int const i = START[j];
        c = B[c];
        for (int p = i; p < i + SIZE[j] - 1; ++p) {
            int const q = F[p];
            int const r = B[p];
            B[q] = p;
            F[r] = p;
            ++C[L[p]];
        }
    }
    
A8: // Unremove l
    c = F[l^1];
    while (c >= n2) {
        int const j = C[c];
        int const i = SIZE[j];
        SIZE[j] = i + 1;
        c = c[F];
    }
    goto A5;
}

//----------------------------------------------------------------------------
// SAT Algoritm B

typedef struct {} satb;

bool sat_b(int const n, vector<vector<int>> const& R) {
    int const m = R.size();
    int const m2 = sum_sizes(R);

    int L[m2];
    int START[m + 1];
    int LINK[m + 1];
    int W[n + n + 2];

    fill(W, W + n + n + 2, 0);

    int p = m2 - 1;
    START[0] = p + 1;
    LINK[0] = 0;
    for (int j = 0; j < m; ++j) {
        for (int i = 0; i < R[j].size(); ++i) {
            int l = R[j][i] << 1;

            if (l < 0) {
                l = (-l)^1;
            }

            L[p] = l;
            --p;
        }
        START[j + 1] = p + 1;
        int const l = L[p + 1];
        LINK[j + 1] = W[l];
        W[l] = j + 1;
    }

B1: // Initialise
    profile<satb> prof;
    int M[n + 1];
    int d = 1;
    int l;

B2: // Finish or choose
    if (d > n) {
        int X[n + 1];
        for (int j = 1; j < d; ++j) {
            X[j] = 1 ^ (M[j] & 1);
            cout << X[j];
        }
        if (verify(R, X)) {
            cout << " VERIFIED";
        }
        return true;
    }
    M[d] = ((W[d << 1] == 0) || (W[(d << 1) + 1] != 0)) ? 1 : 0;
    l = (d << 1) + M[d];

B3: // Remove l if possible
    int j = W[l^1];
    while (j != 0) {
        int const i = START[j];
        int const i2 = START[j - 1];
        int const j2 = LINK[j];
        int k = i + 1;
        while (k < i2) {
            int const l2 = L[k];
            if (((l2 >> 1) > d) || (((l2 + M[l2 >> 1]) & 1) == 0)) {
                L[i] = l2;
                L[k] = l^1;
                LINK[j] = W[l2];
                W[l2] = j;
                j = j2;
                goto next;
            }
            ++k;
        }
        W[l^1] = j;
        goto B5;
next:
        continue;
    }

B4: // Advance
    W[l^1] = 0;
    ++d;
    goto B2;

B5: // Try again
    if (M[d] < 2) {
        M[d] = 3 - M[d];
        l = (d << 1) + (M[d] & 1);
        goto B3;
    }

B6: // Backtrack
    if (d == 1) {
        return false;
    }
    --d;
    goto B5;
}

//----------------------------------------------------------------------------
// SAT Algoritm D

class sat_d {
    vector<vector<int>> const& R;
    int const n;
    int const m;
    int const m2;
    int *const L;
    int *const START;
    int *const LINK;
    int *const W;
    int *const X;

public:
    sat_d(sat_d const&) = delete;
    sat_d(sat_d&&) = delete;
    sat_d& operator= (sat_d const&) = delete;

    sat_d(int const n, vector<vector<int>> const& R)
    : R(R), n(n)
    , m(R.size())
    , m2(sum_sizes(R))
    , L(new int[m2])
    , START(new int[m + 1])
    , LINK(new int[m + 1])
    , W(new int[n + n + 2])
    , X(new int[n + 1])
    {
        fill(W, W + n + n + 2, 0);

        int p = m2 - 1;
        START[0] = p + 1;
        LINK[0] = 0;
        for (int j = 0; j < m; ++j) {
            for (int i = R[j].size() - 1; i >= 0; --i) {
                int l = R[j][i] << 1;

                if (l < 0) {
                    l = (-l)^1;
                }

                L[p] = l;
                --p;
            }
            START[j + 1] = p + 1;
            int const l = L[p + 1];
            LINK[j + 1] = W[l];
            W[l] = j + 1;
        }
    }

    ~sat_d() {
        delete[] L;
        delete[] START;
        delete[] LINK;
        delete[] W;
        delete[] X;
    }

    friend ostream& operator << (ostream& os, sat_d const& that) {
        os << "L: ";
        for (int j = 0; j < that.m2; ++j) {
            os << that.L[j];
            if (j < that.m2 - 1) {
                os << ",";
            }
        }
        os << "\n";

        os << "START: ";
        for (int j = 0; j <= that.m; ++j) {
            os << that.START[j];
            if (j < that.m) {
                os << ",";
            }
        }
        os << "\n";

        os << "W: ";
        for (int j = 0; j < 2 * that.n + 2; ++j) {
            os << that.W[j];
            if (j < 2 * that.n + 1) {
                os << ",";
            }
        }
        os << "\n";

        os << "LINK: ";
        for (int j = 0; j <= that.m; ++j) {
            os << that.LINK[j];
            if (j < that.m) {
                os << ",";
            }
        }
        os << "\n";

        return os;
    }

    int watching_all_false(int const l) {
        for (int j = W[l]; j != 0; j = LINK[j]) {
            for (int p = START[j] + 1; p < START[j - 1]; ++p) {
                if (X[L[p] >> 1] != (L[p] & 1)) {
                    goto unforced;
                }
            }
            return 1;
            unforced: continue;
        }
        return 0;
    }

    bool operator() () {
    D1: // Initialise
        profile<sat_d> prof;
        int M[n + 1];
        int H[n + 1];
        int NEXT[n + 1];
        int d = 0;
        int h = 0;
        int t = 0;

        M[0] = 0;
        int k;
        for (k = n; k > 0; --k) {
            X[k] = -1;
            if (W[k + k] != 0 || W[k + k + 1] != 0) {
                NEXT[k] = h;
                h = k;
                if (t == 0) {
                    t = k;
                }
            }
        }
        if (t != 0) {
            NEXT[t] = h;
        }

    D2: // Is successful
        if (t == 0) {
            for (int j = 1; j <= n; ++j) {
                if (X[j] >= 0) {
                    cout << X[j];
                } else {
                    cout << "-";
                }
            }
            if (verify(R, X)) {
                cout << " VERIFIED";
            }
            return true;
        }
        k = t;
        
    D3: // Look for unit clauses
        h = NEXT[k];
        int const f0 = watching_all_false(h + h);
        int const f1 = watching_all_false(h + h + 1);
        int const f = f0 + f1 + f1;
        if (f == 3) {
            goto D7;
        } else if (f > 0) {
            M[d + 1] = f + 3;
            t = k;
            goto D5;
        } else if (h != t) {
            k = h;
            goto D3;
        }

    D4: // Two way branch
        h = NEXT[t];
        M[d + 1] = (W[h + h] == 0 || W[h + h + 1] != 0) ? 1 : 0;

    D5: // Move on
        ++d;
        k = h;
        H[d] = k;
        if (t == k) {
            t = 0;
        } else {
            h = NEXT[k];
            NEXT[t] = h;
        }

    D6: { // Update watches
            int const b = (M[d] + 1) & 1;
            X[k] = b;
        
            int const l = k + k + b;
            int j = W[l];
            W[l] = 0;
            while (j != 0) {
                int const j2 = LINK[j];
                int const i = START[j];
                int p = i + 1;
                if (p < START[j - 1]) {
                    while (X[L[p] >> 1] == (L[p] & 1)) {
                        ++p;
                        if (p == START[j - 1]) {
                            break;
                        }
                    }
                }
                int const l2 = L[p];
                L[p] = l;
                L[i] = l2;
                p = W[l2];
                int const q = W[l2^1];
                if (X[l2 >> 1] < 0 && p == 0 && q == 0) {
                    if (t == 0) {
                        h = l2 >> 1;
                        t = h;
                        NEXT[t] = h;
                    } else {
                        NEXT[l2 >> 1] = h;
                        h = l2 >> 1;
                        NEXT[t] = h;
                    }
                }
                LINK[j] = p;
                W[l2] = j;
                j = j2;
            }
        }

        goto D2;

    D7: // Backtrack
        t = k;
        while (M[d] >= 2) {
            k = H[d];
            X[k] = -1;
            if ((W[k + k] != 0) || (W[k + k + 1]) != 0) {
                NEXT[k] = h;
                h = k;
                NEXT[t] = h;
            }
            --d;
        }

    D8: // Is failure
        if (d > 0) {
            M[d] = 3 - M[d];
            k = H[d];
            goto D6;
        }

        return false;
    }
};

//----------------------------------------------------------------------------
// SAT Algoritm L *FIXME* Work In Progress

int literal(int const x) {
    if (x < 0) {
        return ((-x) << 1) | 1;
    } else {
        return x << 1;
    }
}

ostream& show_lit(ostream &os, int l) {
    int const x = l >> 1;
    if ((l & 1) == 0) {
        os << x;
    } else {
        os << x << "^";
    }
    return os;
}

int ternary_count(vector<vector<int>> const& R) {
    int c = 0;
    for (int j = 0; j < R.size(); ++j) {
        if (R[j].size() == 3) {
            ++c;
        }
    }
    return c;
}

int distinct_unit_literals(int const n, vector<vector<int>> const& R) {
    int unit_literals = 0;
    int UNIT[n + n + 2];
    for (int j = 0; j < n + n + 2; ++j) {
        UNIT[j] = 0;
    }
    for (int j = 0; j < R.size(); ++j) {
        if (R[j].size() == 1) {
            int const l = literal(R[j][0]);
            if (UNIT[l^1] != 0) {
                throw runtime_error("unit clause conflict");
            }
            if (UNIT[l] == 0) {
                ++unit_literals;
            }
            ++UNIT[l];
        }
    }
    return unit_literals;
}

class sat_l {
    static int constexpr RT = numeric_limits<int>::max() - 1;
    static int constexpr NT = RT - 2;
    static int constexpr PT = NT - 2;

    vector<vector<int>> const& R;
    int const n;
    int const m;
    int const m3;
    int const U;
    int *const LINK;
    pair<int, int> *const TMEM;
    pair<int, int> *const TIMP;
    vector<int> *const BIMP;
    int *const FORCE;
    int *const VAR;
    int *const INX;

public:
    sat_l(int const n, vector<vector<int>> const& R)
    : R(R), n(n)
    , m(R.size())
    , m3(ternary_count(R))
    , U(distinct_unit_literals(n, R))
    , LINK(new int[3 * m3])
    , TMEM(new pair<int, int>[3 * m3])
    , TIMP(new pair<int, int>[n + n + 2])
    , BIMP(new vector<int>[n + n + 2])
    , FORCE(new int[U])
    , VAR(new int[n])
    , INX(new int[n + 1])
    {
        for (int j = 0; j < m; ++j) {
            if (R[j].size() == 3) {
                int const u = literal(R[j][0]);
                int const v = literal(R[j][1]);
                int const w = literal(R[j][2]);
                ++(TIMP[u^1].second);
                ++(TIMP[v^1].second);
                ++(TIMP[w^1].second);
            } else {
                throw runtime_error("only 3SAT supported.\n");
            }
        }
        
        {
            int j = 0;
            int l = n + n + 1;
            while (l >= 2) {
                TIMP[l].first = j;
                j += TIMP[l].second;
                TIMP[l].second = 0;
                --l;
            }
            TIMP[l].first = j;
        }

        for (int j = m - 1; j >= 0; --j) {
            int const u = literal(R[j][0]);
            int const v = literal(R[j][1]);
            int const w = literal(R[j][2]);
            int const us = TIMP[u^1].second;
            int const uu = TIMP[u^1].first + us;
            int const vs = TIMP[v^1].second;
            int const vv = TIMP[v^1].first + vs;
            int const ws = TIMP[w^1].second;
            int const ww = TIMP[w^1].first + ws;
            TIMP[u^1].second = us + 1;
            TMEM[uu].first = v;
            TMEM[uu].second = w;
            LINK[uu] = vv;
            TIMP[v^1].second = vs + 1;
            TMEM[vv].first = u;
            TMEM[vv].second = w;
            LINK[vv] = ww;
            TIMP[w^1].second = ws + 1;
            TMEM[ww].first = u;
            TMEM[ww].second = v;
            LINK[ww] = uu;
        }

        INX[0] = 0;
        for (int j = 0; j < n; ++j) {
            VAR[j] = j + 1;
            INX[j + 1] = j;
        }
    }

    ~sat_l() {
        delete[] LINK;
        delete[] TMEM;
        delete[] TIMP;
        delete[] BIMP;
        delete[] FORCE;
        delete[] VAR;
        delete[] INX;
    }

    friend ostream& operator << (ostream& os, sat_l const& that) {
        os << "TIMP: ";
        for (int j = 2; j < that.n + that.n + 2; ++j) {
            show_lit(os, j);
            os << "{";
            for (int i = that.TIMP[j].first; i < that.TIMP[j - 1].first; ++i) {
                os << that.TMEM[i].first << "/" << that.TMEM[i].second;
                if (i < that.TIMP[j - 1].first - 1) {
                    os << ", ";
                }
            }
            os << "} ";
            show_lit(os, that.LINK[j]);
            if (j < that.n + that.n + 1) {
                os << ", ";
            }
        }
        os << "\n";

        os << "BIMP: ";
        for (int j = 0; j < that.n + that.n + 2; ++j) {
            cout << j << " {";
            for (int i = 0; i < that.BIMP[j].size(); ++i) {
                os << that.BIMP[j][i];
                if (i < that.BIMP[j].size() - 1) {
                    os << ", ";
                }
            }
            cout << "}";
            if (j < that.n + that.n + 1) {
                os << ", ";
            }
        }
        os << "\n";

        os << "FORCE: ";
        for (int j = 0; j < that.U; ++j) {
            os << that.FORCE[j];
            if (j < that.U - 1) {
                os << ", ";
            }
        }
        os << "\n";

        os << "VAR: ";
        for (int j = 0; j < that.n; ++j) {
            os << that.VAR[j];
            if (j < that.n - 1) {
                os << ", ";
            }
        }
        os << "\n";

        os << "INX: ";
        for (int j = 0; j < that.n + 1; ++j) {
            os << that.INX[j];
            if (j < that.n) {
                os << ", ";
            }
        }
        os << "\n";

        return os;
    }

/*
    void refine_heuristics() {
        int const N = n - F;

        double h = 0;
        for (int j = 2; j < n + n + 2; ++j) {
            h += H[j];
        }
        h /= N + N;
        

        for (int j = 2; j < n + n + 2; ++j) {
            H[j] = 

*/

/*
    bool operator() () {
        int BRANCH[n];

    L1: // Initialise
        int d = 0;
        int F = 0;
        int I = 0;
        int ISTAMP = 0;
        int l;

    L2: // New node
        BRANCH[d] = -1;
        if (U > 0) {
            goto L5;
        }
        // X
        if (F == n) {
            // all done;
            return true;
        }

    L3:
        // choose l (579)
        if (l == 0) {
            ++d;
            goto L2;
        } 
        DEC[d] = l;
        BACKF[d] = F;
        BACKI[d] = I;
        BRANCH[d] = 0;

    L4:
        U = 1;
        FORCE[0] = l;
    
    L5:
        T = NT;
        G = E = F;
        ++ISTAMP;
        CONFLICT = L11;
        // binary propagate (62)
        U = 0;

    L6:
        if (G == E) {
            goto L10;
        }
        L = R[G++];

    L7:
        X = L >> 1;
        VAL[X] = RT + L & 1;
        // remove X (ex 563)

        for (int j = TIMP[L].first; j < TIMP[L - 1].first; ++j) {
            pair<int, int> &tj = TMEM[j];
            int const u = tj.first;
            int const v = tj.second;
            int const vu = VAL[u >> 1];
            int const vv = VAL[v >> 1];
            bool const u_fixed = (vu >= T);
            bool const v_fixed = (vv >= T);
            if (u_fixed && v_fixed) {
                bool const u_false = (vu & 1) == ((u^1) & 1);
                bool const v_false = (vv & 1) == ((v^1) & 1);
                if (u_false && v_false) {
                    goto CONFLICT;
                }
            } else if (u_fixed) {
                bool const u_false = (vu & 1) == ((u^1) & 1);
                if (u_false) {
                    // (62) l <- v
                } 
            } else if (v_fixed) {
                bool const v_false = (vv & 1) == ((v^1) & 1);
                if (v_false) {
                    // (62) l <- u
                }
            } else {
                // L9
            }
        }
    }
*/
};

//----------------------------------------------------------------------------
// Consider how the above solvers might fit in the following generic framework.

class Solver {
    vector<vector<int>> F;
    vector<int> M;

public:
    Solver(vector<vector<int>> F) : F(F) {}
    void apply_decide();
    void apply_propagate();
    void apply_conflict();
    void apply_explain();
    void apply_learn();
    void apply_backtrack();
    void apply_forget();
    void apply_restart();
};

//----------------------------------------------------------------------------

int main(int const argc, char const *argv[]) {
    if (argc < 1) {
        cerr << "no input files\n";
    } else {
        for (int i = 1; i < argc; ++i) {
            try {
                fstream in(argv[i], ios_base::in);
                cnf_parser cnf(in);

                cout << argv[i];

                if (in.is_open()) {
                    vector<vector<int>> clauses;
                    int const n = cnf(clauses);
                    if (n > 0) {
                        /*
                        cout << "\nA: ";
                        if (sat_a(n, clauses)) {
                            cout << " SAT ";
                        } else {
                            cout << " UNSAT ";
                        }
                        cout << "in " << profile<sata>::report() << "us\n";
                        */
                     
                        /*   
                        cout << "\nB: ";
                        if (sat_b(n, clauses)) {
                            cout << " SAT ";
                        } else {
                            cout << " UNSAT ";
                        }
                        cout << "in " << profile<satb>::report() << "us\n";
                        */
                        
                        {
                            sat_d d(n, clauses);
                            cout << "\nD: ";
                            if (d()) {
                                cout << " SAT ";
                            } else {
                                cout << " UNSAT ";
                            }
                            cout << "in " << profile<sat_d>::report() << "us\n";
                        }

                        /*{
                            sat_l l(n, clauses);
                            cout << "\nL: ";
                            cout << l;
                            cout << "\n";
                        }*/
                    } else {
                        cerr << "EMPTY\n";
                    }
                    in.close();
                } else {
                    cerr << "could not open " << argv[i] << "\n";
                    return 1;
                }
            } catch (parse_error& e) {
                cerr << argv[i] << ": " << e.what()
                    << " '" << e.exp
                    << "' found ";
                if (is_print(e.sym)) {
                    cerr << "'" << static_cast<char>(e.sym) << "'";
                } else {
                    cerr << "0x" << hex << e.sym;
                }
                cerr << " at line " << e.row
                    << ", column " << e.col << "\n";
                return 2;
            } catch (format_error& e) {
                cerr << argv[i] << ": " << e.what()
                    << " at line " << e.row << "\n";
                return 3;
            }
        }
    }
}
