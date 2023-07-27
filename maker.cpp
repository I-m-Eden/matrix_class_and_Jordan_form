#include <bits/stdc++.h>
using namespace std;
#define ref(i,x,y)for(int i=x;i<=y;++i)
#define SZ(x) (int)x.size()
#define pb push_back
#define mp make_pair
#define fi first
#define se second
typedef long long LL;
typedef pair<int,int> PII;
const int N=101;
int n,p;
void inc(int&a,int b){a+=b;if(a>=p)a-=p;}
void dec(int&a,int b){a-=b;if(a<0)a+=p;}
int mul(int a,int b){return (LL)a*b%p;}
int mi(int a,int b){
	int s=1;
	for(;b;b>>=1,a=(LL)a*a%p)
		if(b&1)s=(LL)s*a%p;
	return s;
}
vector<int> add_poly(vector<int> a,vector<int> b){
	vector<int> s=a;s.resize(SZ(b));
	ref(i,0,SZ(b)-1)inc(s[i],b[i]);
	while(SZ(s)>1&&s.back()==0)s.pop_back();return s;
}
class mat{
public:
	int n,a[N][N];
	mat(){n=0;memset(a,0,sizeof a);}
	mat(int _n,int s=0){
		n=_n;memset(a,0,sizeof a);
		ref(i,0,n-1)a[i][i]=s;
	}
	mat operator-(const mat&b){
		mat s=*this; assert(s.n==b.n);
		ref(i,0,s.n-1)ref(j,0,s.n-1) dec(s.a[i][j],b.a[i][j]);
		return s;
	}
	mat operator*(const mat&b){
		mat s(n); assert(n==b.n);
		ref(i,0,n-1)ref(j,0,n-1)if(a[i][j])
			ref(k,0,n-1)if(b.a[j][k])
				inc(s.a[i][k],mul(a[i][j],b.a[j][k]));
		return s;
	}
	mat simplify(){
		mat s=*this;
		for(int i=0,ii=0;i<s.n;++i){
			if(!s.a[ii][i])ref(j,ii+1,s.n-1)if(s.a[j][i]){
				ref(k,i,s.n-1)swap(s.a[ii][k],s.a[j][k]);
				break;
			}
			if(s.a[ii][i]){
				int w=mi(s.a[ii][i],p-2);
				ref(j,i+1,s.n-1)s.a[ii][j]=mul(s.a[ii][j],w);
				ref(j,ii+1,s.n-1)if(s.a[j][i]){
					ref(k,i+1,s.n-1)dec(s.a[j][k],mul(s.a[j][i],s.a[ii][k]));
					s.a[j][i]=0;
				}
				ref(j,i+1,s.n-1)s.a[ii][j]=mul(s.a[ii][j],s.a[ii][i]);
				ii++;
			}
		}
		return s;
	}
	mat inv(){
		mat s(n*2,0),res(n,0);
		ref(i,0,n-1)ref(j,0,n-1)s.a[i][j]=a[i][j];
		ref(i,0,n-1)s.a[i][i+n]=1;
		s=s.simplify();
		for(int i=n-1;i>=0;--i){
			int w=mi(s.a[i][i],p-2);s.a[i][i]=1;
			ref(j,0,n-1)s.a[i][j+n]=mul(s.a[i][j+n],w);
			ref(j,0,i-1){
				ref(k,0,n-1)dec(s.a[j][k+n],mul(s.a[j][i],s.a[i][k+n]));
				s.a[j][i]=0;
			}
		}
		ref(i,0,n-1)ref(j,0,n-1)res.a[i][j]=s.a[i][j+n];
		return res;
	}
	int det(){
		mat s=simplify(); int res=1;
		ref(i,0,s.n-1)res=mul(res,s.a[i][i]); return res;
	}
	int rank(){
		mat s=simplify();
		ref(i,0,s.n-1)ref(j,0,s.n-1){
			if(s.a[i][j])break;
			if(j==s.n-1)return i;
		}
		return s.n;
	}
	vector<int> minimal_poly(){
		vector<pair<vector<int>,int> >s;mat b(n,1);
		int len=n*n;
		for(int ti=0;ti<=n;++ti,b=b*(*this)){
			vector<int> w;
			ref(i,0,n-1)ref(j,0,n-1)w.pb(b.a[i][j]);
			ref(i,0,n)w.pb(ti==i);
			int pos=0;while(pos<len&&!w[pos])pos++;
			ref(i,0,SZ(s)-1)if(s[i].se==pos){
				ref(j,pos+1,SZ(w)-1)dec(w[j],mul(w[pos],s[i].fi[j]));
				w[pos]=0;
				while(pos<len&&!w[pos])pos++;
			}
			if(pos==len){
				vector<int> res;
				ref(j,len,len+n)res.pb(w[j]);
				while(!res.back())res.pop_back();
				return res;
			}
			int v=mi(w[pos],p-2);
			ref(j,pos,SZ(w)-1)w[j]=mul(w[j],v);
			s.pb(mp(w,pos));
		}
	}
	vector<int> poly(){
		mat s=*this;
		vector<int> c,res,r;
		ref(i,0,n)c.pb((mat(s.n,i)-s).det());
		ref(i,0,n){
			cout<<i<<"-->"<<c[i]<<endl;
			int v=1;
			ref(j,0,n)if(j!=i)v=mul(v,p+i-j);
			v=mul(c[i],mi(v,p-2));
			r.clear();r.pb(v);
			ref(j,0,n)if(j!=i){
				r.pb(0);
				for(int l=SZ(r)-1;l>=0;--l){
					int w=mul(r[l],j);
					if(l)r[l]=r[l-1];else r[l]=0;
					dec(r[l],w);
				}
			}
			res=add_poly(res,r);
		}
		return res;
	}
};
mat mip(mat a,int b){
	mat s(n,1);
	for(;b;b>>=1,a=a*a)
		if(b&1)s=s*a;
	return s;
}
mat A;
int seedn[2]={2,10};
int seedp[2]={10007,10007};
int seed[2][10][2]={
		{{0,2},{1,3},{0,0},{0,0},{0,0},{0,0},{0,0},{0,0},{0,0},{0,0}},
		{{0,2},{0,5},{1,4},{1,3},{1,5},{2,2},{2,5},{3,1},{4,1},{5,5}}
	};
int main(int argn,char*argc[]){
	srand(time(0));
	int id=1;
	n=0,p=seedp[id];ref(i,0,seedn[id]-1)n+=seed[id][i][1];
	mat A(n,0),B(n,0),C(n,0);
	int v1=rand()%p,v2;
	for(int i=0,sum=0;i<seedn[id];sum+=seed[id][i][1],++i){
		v2=rand()%p;if(i>0&&seed[id][i][0]!=seed[id][i-1][0])v1=rand()%p;
		for(int j=sum;j<sum+seed[id][i][1];++j){
			A.a[j][j]=v1;C.a[j][j]=v1;
			if(j<sum+seed[id][i][1]-1)A.a[j][j+1]=v2;
		}
	}
	while(1){
		for(int i=0;i<n;i++)for(int j=0;j<n;++j)
			B.a[i][j]=rand()%p;
		if(B.det()!=0)break;
	}
	mat niB=B.inv();
	mat ck=B*niB;
	ref(i,0,n-1)ref(j,0,n-1)assert(ck.a[i][j]==(i==j));
	mat s1=B*A*niB;
	mat s2=B*C*niB;
	//mat s1=A,s2=C;
	ofstream fout("1.in");
	fout<<n<<" "<<p<<endl;
	ref(i,0,n-1){
		ref(j,0,n-1)fout<<s1.a[i][j]<<" ";
		fout<<endl;
	}
	fout.close();
	ofstream fout2("1.ans");
	ref(i,0,n-1){
		ref(j,0,n-1)fout2<<s2.a[i][j]<<" ";
		fout2<<endl;
	}
	fout2.close();
}