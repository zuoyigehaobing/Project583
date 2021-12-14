#include <vector>
#include <algorithm>
#include <limits.h>

using namespace std;

double mediann(vector<int>&a,vector<int>&b){
    int m=a.size();
    int n=b.size();
    if(m>n)
        return mediann(b,a);
    int l=0,r=m;
    while(l<=r){
        int partx=l+(r-l)/2;
        int party=(m+n+1)/2-partx;
        int maxlx=(partx==0)?INT_MIN:a[partx-1];
        int minrx=(partx==m)?INT_MAX:a[partx];
        int maxly=(party==0)?INT_MIN:b[party-1];
        int minry=(party==n)?INT_MAX:b[party];
        if(maxlx<=minry&&maxly<=minrx){
            if((m+n)%2==0)
                return (double)(max(maxlx,maxly)+min(minrx,minry))/2;
            else
                return (double)(max(maxlx,maxly));
        }else if(maxlx>minry)
            r=partx-1;
        else
            l=partx+1;
    }
    return -1.0;
}
double findMedianSortedArrays(vector<int>& nums1, vector<int>& nums2) {
    double ans;
    ans=mediann(nums1,nums2);
    return ans;
}

int main() {
  vector<int> a = {0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 32, 34, 36, 38, 40, 42, 44, 46, 48, 50, 52, 54, 56, 58, 60, 62, 64, 66, 68, 70, 72, 74, 76, 78, 80, 82, 84, 86, 88, 90, 92, 94, 96, 98};
  vector<int> b = {1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25, 27, 29, 31, 33, 35, 37, 39, 41, 43, 45, 47, 49, 51, 53, 55, 57, 59, 61, 63, 65, 67, 69, 71, 73, 75, 77, 79, 81, 83, 85, 87, 89, 91, 93, 95, 97, 99};
  double res = findMedianSortedArrays(a,b);
  return 0;
}
