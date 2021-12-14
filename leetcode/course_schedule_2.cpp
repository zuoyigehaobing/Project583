#include <utility>
#include <vector>
#include <queue>          // std::queue

using namespace std;
vector<int> findOrder(int numCourses, vector<pair<int, int>>& prerequisites) {
    vector<int> res;
    vector<int> indegree(numCourses,0);
    vector<vector<int>> graph(numCourses,vector<int>());

    for(auto pre:prerequisites)
    {
        graph[pre.second].push_back(pre.first);
        indegree[pre.first]++;
    }
    queue<int> que;
    for(int i=0;i<indegree.size();i++)
        if(indegree[i]==0)
            que.push(i);

    while(!que.empty())
    {
        int u = que.front();que.pop();
        res.push_back(u);
        for(auto v:graph[u])
        {
            indegree[v]--;
            if(indegree[v] == 0)
                que.push(v);
        }
    }
    if(res.size()==numCourses)
        return res;
    else
        return vector<int>();
}
int main () {
  vector<pair<int,int>> prerequisites;
  pair <int,int> p1 (1,0);
  pair <int,int> p2 (2,0);
  pair <int,int> p3 (3,1);
  pair <int,int> p4 (3,2);
  prerequisites.push_back(p1);
  prerequisites.push_back(p2);
  prerequisites.push_back(p3);
  prerequisites.push_back(p4);
  int numCourses = 4;
  findOrder(numCourses, prerequisites);
  return 0;
}
