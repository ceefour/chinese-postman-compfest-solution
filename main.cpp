#include <bits/stdc++.h>
#include <iostream>
#include <fstream>
using namespace std;
typedef long long LL;
typedef vector<int> vi;
typedef pair<int, int> PII;
typedef pair<LL, LL> PLL;
#define rep(i, a, b) for(int i = a; i < (b); ++i)
#define trav(a, x) for(auto& a : x)
#define all(x) begin(x), end(x)
#define sz(x) (int)(x).size()
#define pb push_back
#define remove erase
#define fi first
#define se second

const LL LINF = 4557430888798830399LL;

const int MAXN = 1000;

int N;
int part[MAXN+5];
int deg[2][MAXN+5];
int dir[MAXN+5][MAXN+5];

vector <int> curans;

LL dis[MAXN+5][MAXN+5];

vector <PII> edge[MAXN+5];
vector <pair<PII, int>> edges;


/** MCMF Template starts here */
struct dte{
    LL to, cost, cap, flow, backEdge;
};

PII newEdge;

/* Minimum cost maximum flow */
struct MCMF {
    LL s, e, n;
    vector<vector<dte>> edge;
    MCMF(LL _s, LL _e, LL _n) {
        s = _s, e = _e, n = _n;
        cout << "MCMF s(pasti 0)=" << _s << " e(jumlah city+1)=" << _e << " n(jumlah city+2)=" << _n << "\n";
        edge.resize(n);
    }
    void addEdge(/*source city*/ LL u, /*dest city*/ LL v, /*difference of degree*/ LL cap, LL cost) {
        cout << "addEdge " << (u+1) << " to " << (v+1) << " : diff=" << cap << " cost=" << cost << endl;
        dte e1 = { v, cost, cap, 0,(LL)(edge[v].size())};
        dte e2 = { u, -cost, 0, 0,(LL)(edge[u].size())};
        edge[u].push_back(e1); edge[v].push_back(e2);
    }
    PLL minCostMaxFlow() {
        LL flow = 0, cost = 0;
        vector<LL> vis(n), from(n), from_edge(n), dist(n);
        deque<LL> q;
        while (1) {
            for (int i = 0; i < n; i++)
                vis[i] = 2, dist[i] = LINF, from[i] = -1;
            vis[s] = 1; q.clear(); q.push_back(s); dist[s] = 0;
            while (!q.empty()) {
                LL pos = q.front(); q.pop_front(); vis[pos] = 0;
                for (int i = 0; i < edge[pos].size(); i++) {
                    dte nx = edge[pos][i];
                    if (nx.flow >= nx.cap || dist[nx.to] <= dist[pos] + nx.cost) continue;
                    LL to = nx.to; dist[to] = dist[pos] + nx.cost;
                    from[to] = pos; from_edge[to] = i;
                    if (vis[to] == 1) continue;
                    if (!vis[to] || (!q.empty() && dist[q.front()] > dist[to]))
                        q.push_front(to);
                    else q.push_back(to);
                    vis[to] = 1;
                }
            }
            if (dist[e] == LINF) break;
            LL it = e, addflow = LINF;
            while (it != s) {
                addflow = min(addflow, edge[from[it]][from_edge[it]].cap- edge[from[it]][from_edge[it]].flow);
                it = from[it];
            }
            it = e;
            while (it != s) {
                edge[from[it]][from_edge[it]].flow += addflow;
                edge[it][edge[from[it]][from_edge[it]].backEdge].flow -= addflow;
                cost += edge[from[it]][from_edge[it]].cost * addflow;
                it = from[it];
            }
            flow += addflow;
        }
        return {cost,flow};
    }
    void getpath(int st, int ed){
        newEdge = {-1,-1};
        while(st != ed){
            bool changed = 0;
            for(auto &nx : edge[st]){
                if(nx.flow > 0){
                    if(part[st] == -1 && newEdge.fi == -1) newEdge.fi = st;
                    newEdge.se = st;
                    nx.flow--;
                    st = nx.to;
                    changed = 1;
                    break;
                }
            }
            if(!changed) break;
        }
    }
};

/** MCMF template ends here */

/**
 * Push the path (shortest path from a to b) to curans in reverse order
 */
void getPath(int a, int b){
    vector <int> tmp;
    while(a != b){
        for(int i = 1;i <= N;i++){
            if(dir[a][i] && dis[a][i]+dis[i][b] == dis[a][b]){
                tmp.pb(dir[a][i]);
                a = i;
                break;
            }
        }
    }
    reverse(all(tmp));
    trav(cur, tmp) curans.pb(cur);
}

/** Push euler circuit path starting from pos and ending on pos */
void hierholzer(int pos){
    while(!edge[pos].empty()){
        PII nx = edge[pos].back();
        edge[pos].pop_back();
        hierholzer(nx.fi);
        // cout << pos << " " << nx.fi << " " << nx.se << endl;
        if(nx.se) curans.pb(nx.se);
        else getPath(pos, nx.fi);
    }
}

/** Floyd warshall */
void generateDist(/* number of cities */ int n){
    // rep(i,1,n+1) rep(j,1,n+1) cout << ((dis[i][j] == LINF) ? "∞" : to_string(dis[i][j])) << " \n"[j == n];
    rep(k,1,n+1) rep(i,1,n+1) rep(j,1,n+1) dis[i][j] = min(dis[i][j], dis[i][k]+dis[k][j]);
    // rep(i,1,n+1) rep(j,1,n+1) cout << ((dis[i][j] == LINF) ? "∞" : to_string(dis[i][j])) << " \n"[j == n];
}


/** Solve Chinese postman problem */
pair<LL, vi> solveProblem(int n, int m, LL tot = 0){
    cout << "Solving n=" << (n) << " m=" << (m) << " tot=" << tot << "\n";

    // Reset all stuffs
    curans.clear();
    rep(i,0,n+1) edge[i].clear(), deg[0][i] = deg[1][i] = part[i] = 0;
    rep(i,0,n+1) rep(j,0,n+1) dis[i][j] = LINF, dir[i][j] = 0;
    rep(i,0,n+1) dis[i][i] = 0;

    /* for all roads */
    rep(i,0,m){

        /*
        curedge = {<source_city, dest_city> : weight}
        */
        pair<PII,LL> curedge = edges[i];
        /*
        deg 0 : keluar
        deg 1 : masuk
        deg[0..1][idx_city] = degree of vertex
        */
        deg[0][curedge.fi.fi]++, deg[1][curedge.fi.se]++;
        /*
        dis[idx source city][dest city] = jarak terpendek
        */
        dis[curedge.fi.fi][curedge.fi.se] = min(dis[curedge.fi.fi][curedge.fi.se], curedge.se);
        /*
        kalau distance dari kota A ke B == bobot edge ini:
        dir[source city][dest city] = idx jalan + 1 // rute langsung terpendek lewat jalan ini dari kota A ke B, ga muter2
        */
        if(dis[curedge.fi.fi][curedge.fi.se] == curedge.se) dir[curedge.fi.fi][curedge.fi.se] = i+1;
        /*
        edge : vector[source city] = pair<dest city, idx jalan>
        */
        edge[curedge.fi.fi].pb({curedge.fi.se, i+1});
        //cout << edge[curedge.fi.fi] << "\n";
    }

    /* memastikan dis(tance) terpendek dari setiap kombinasi kota I -> kota perantara K -> J.
    masuk ke variable dis */
    generateDist(n);

    // This graph is not strongly connected
    // for each combination of city I * J:
    // checking kalau tidak mungkin dari kota I menuju J, maka program berhenti
    rep(i,1,n+1) rep(j,1,n+1) if(dis[i][j] == LINF) {
      cout << "No route from city " << (i+1) << " to " << (j+1) << " so will not recurse solve\n";
      return {LINF, {}};
    }

    /*
    _s = 0
    _e = jumlah kota + 1
    _n = jumlah kota + 2
    */
    MCMF solve(0, n+1, n+2);
    int degdiff[2] = {0,0};

    for(int i = 1;i <= n;i++){
        /* diff : selisih antara degree masuk(1) - degree keluar(0) */
        int diff = deg[1][i]-deg[0][i];
        if(!diff) {
          cout << "Degree masuk & keluar for city " << (i+1) << " is ZERO\n";
          continue;
        }
        cout << "Degree masuk & keluar for city " << (i+1) << " is " << diff << "\n";
        degdiff[(diff > 0)] += abs(diff);
        // selisih degree harus selalu positif untuk dari kota 1 -> I,
        // kalo negatif maka jadi edge dari kota I+1 -> kota terakhir
        /*
        part[idx city] : awalnya 0, lalu bisa jadi -1 atau 1
        */
        if(diff > 0) {
          solve.addEdge(0, i, diff, 0), part[i] = -1;
          cout << "  part " << (i+1) << " = -1\n";
        }
        else {
          solve.addEdge(i, n+1, -diff, 0), part[i] = 1;
          cout << "  part " << (i+1) << " = 1\n";
        }
    }

    rep(i,1,n+1) rep(j,1,n+1) if(part[i] == -1 && part[j] == 1) solve.addEdge(i, j, LINF, dis[i][j]);
    PLL ans = solve.minCostMaxFlow();

    assert(degdiff[0] == degdiff[1]);
    assert(degdiff[0] == ans.se);
    
    // Make new edge based on shortest path mcmf
    rep(i,0,ans.se){
        solve.getpath(0, n+1);
        edge[newEdge.fi].pb({newEdge.se,0});
    }

    // Try to do the hierholzer
    hierholzer(1);

    // Returns the path
    return {tot+ans.fi, curans};

}

// Backtrack the answer
void print(pair <LL, vi> &ans, bool swappedFirst = 0){
    if(ans.fi == LINF) cout << -1 << endl;
    else{
        // cout << "Here" << endl;
        reverse(all(ans.se));
        if(!swappedFirst) cout << "BAIK" << endl;
        else cout << "BURUK" << endl;
        cout << ans.fi << endl;
        cout<<ans.se.size()<<" ";
        LL total_cost = 0;
        rep(i,0,sz(ans.se)) {
          pair<PII,LL> curedge = edges[ans.se[i]];
          cout << ans.se[i] << "(" << curedge.se << ")" << " \n"[i == sz(ans.se)-1];
          total_cost += curedge.se;
        }
        cout << "Total cost: " << total_cost << endl;
    }
}

int main(){

    // read from case1.txt
    // ifstream MyReadFile("case1.txt");

    // Use a while loop together with the getline() function to read the file line by line
    // while (getline (MyReadFile, myText)) {
    //   // Output the text from the file
    //   cout << myText;
    // }

    // Close the file
    // string myText;
    // MyReadFile.close();
    // getline(MyReadFile, myText);
    // cout << myText;

    int n, m;
    LL tot = 0;
    cin >> n >> m; N = n;
    rep(i,0,m){
        int u,v,c; cin >> u >> v >> c;
        edges.pb({{u, v}, c}); tot += c;
        deg[0][u]++; deg[1][v]++;
    }
    cout << "-------- NGECEK YANG BAIK ------\n";
    pair <LL, vi> a = solveProblem(n,m,tot);
    swap(edges[0].fi.fi, edges[0].fi.se);
    print(a);
    cout << "Total BAIK:" << a.fi << endl;
    cout << "-------- NGECEK YANG BURUK ------\n";
    pair <LL, vi> b = solveProblem(n,m,tot);
    print(b, 1);
    cout << "Total BURUK:" << b.fi << endl;

    cout << "BEST:\n";
    if(a.fi <= b.fi) print(a);
    else print(b, 1);
    return 0;
}
