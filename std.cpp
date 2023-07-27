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
const int N=50;
int p,C[N*2+1][N*2+1];
void inc(int&a,int b){a+=b;if(a>=p)a-=p;}
void dec(int&a,int b){a-=b;if(a<0)a+=p;}
int mul(int a,int b){return (LL)a*b%p;}
int mi(int a,int b){
	int s=1;
	for(;b;b>>=1,a=(LL)a*a%p)
		if(b&1)s=(LL)s*a%p;
	return s;
}
void print(vector<int> a){
	ref(i,0,SZ(a)-1)cout<<a[i]<<" ";
	puts("");
}
vector<int> mul_poly(vector<int> a,vector<int> b){
	vector<int> s;s.resize(SZ(a)+SZ(b)-1);
	ref(i,0,SZ(a)-1)ref(j,0,SZ(b)-1)
		inc(s[i+j],mul(a[i],b[j]));
	while(SZ(s)>1&&s.back()==0)s.pop_back();return s;
}
vector<int> add_poly(vector<int> a,vector<int> b){
	vector<int> s=a;s.resize(SZ(b));
	ref(i,0,SZ(b)-1)inc(s[i],b[i]);
	while(SZ(s)>1&&s.back()==0)s.pop_back();return s;
}
vector<int> sub_poly(vector<int> a,vector<int> b){
	vector<int> s=a;s.resize(SZ(b));
	ref(i,0,SZ(b)-1)dec(s[i],b[i]);
	while(SZ(s)>1&&s.back()==0)s.pop_back();return s;
}
vector<int> mod_poly(vector<int> a,vector<int> b){
	int niw=mi(b.back(),p-2);
	ref(i,0,SZ(b)-1)b[i]=mul(b[i],niw);
	for(int i=SZ(a)-1;i>=SZ(b)-1;--i){
		ref(j,0,SZ(b)-1)dec(a[i-SZ(b)+1+j],mul(a.back(),b[j]));
		a.pop_back();
	}
	while(SZ(a)>1&&a.back()==0)a.pop_back();return a;
}
vector<int> div_poly(vector<int> a,vector<int> b){
	int niw=mi(b.back(),p-2);
	ref(i,0,SZ(b)-1)b[i]=mul(b[i],niw);
	ref(i,0,SZ(a)-1)a[i]=mul(a[i],niw);
	vector<int> s;s.resize(SZ(a)-SZ(b)+1);
	for(int i=SZ(a)-1;i>=SZ(b)-1;--i){
		s[i-SZ(b)+1]=a.back();
		ref(j,0,SZ(b)-1)dec(a[i-SZ(b)+1+j],mul(a.back(),b[j]));
		a.pop_back();
	}
	while(SZ(s)>1&&s.back()==0)s.pop_back();return s;
}
vector<int> gcd_poly(vector<int> a,vector<int> b){
	if(SZ(a)<SZ(b))swap(a,b);
	if(SZ(b)==1){if(b[0]==0)return a;else return b;}
	return gcd_poly(b,mod_poly(a,b));
}
vector<int> dif_poly(vector<int> a){
	assert(SZ(a)>1);
	vector<int> s;s.resize(SZ(a)-1);
	ref(i,0,SZ(s)-1)s[i]=mul(a[i+1],i+1);
	return s;
}
pair<vector<int>,vector<int> > inv_poly(vector<int> a,vector<int> b){
	if(SZ(a)==1){
		a[0]=mi(a[0],p-2);
		b.clear();return mp(a,b);
	}
	pair<vector<int>,vector<int> > res=inv_poly(mod_poly(b,a),a);
	vector<int> rb=res.fi,ra=res.se;
	ra=sub_poly(ra,mul_poly(rb,div_poly(b,a))); return mp(ra,rb);
}
vector<int> com_poly(vector<int> a,vector<int> b){
	//cout<<"com"<<endl;
	//print(a);
	//print(b);
	vector<int> res,s;s.pb(1);
	ref(i,0,SZ(a)-1){
		if(SZ(s)>SZ(res))res.resize(SZ(s));
		ref(j,0,SZ(s)-1)inc(res[j],mul(s[j],a[i]));
		s=mul_poly(s,b);
	}
	while(SZ(res)>1&&res.back()==0)res.pop_back();
	return res;
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
vector<PII> solve(vector<int> x){
	vector<PII> res;
	ref(i,0,p-1){
		int tot=0;
		while(1){
			int y=0;
			for(int j=0,w=1;j<SZ(x);++j,w=mul(w,i))
				inc(y,mul(w,x[j]));
			if(y)break;tot++;
			if(!i)ref(j,0,SZ(x)-2)x[j]=x[j+1];else{
				int nii=mi(i,p-2);
				ref(j,0,SZ(x)-2)if(x[j]){
					x[j]=(p-mul(nii,x[j]))%p;
					dec(x[j+1],x[j]);
				}
			}
			x.pop_back();
		}
		if(tot)res.pb(mp(i,tot));
	}
	return res;
}
mat get_ans(vector<int> res,mat A){
	mat ans(A.n),id(A.n,1);
	ref(i,0,SZ(res)-1){
		ref(j,0,A.n-1)ref(k,0,A.n-1)
			inc(ans.a[j][k],mul(id.a[j][k],res[i]));
		id=id*A;
	}
	return ans;
}
void work1(int n,mat A){
	vector<int> mx=A.minimal_poly();
	vector<PII> c=solve(mx);
	//ref(i,0,SZ(c)-1)cout<<c[i].fi<<" "<<c[i].se<<endl;puts("");
	if(SZ(c)==1){
		mat ans(n,c[0].fi);
		ref(i,0,n-1){
			ref(j,0,n-1)cout<<ans.a[i][j]<<" ";
			cout<<endl;
		}
		return;
	}
	vector<int> res;
	ref(i,0,SZ(c)-1){
		vector<int> ss,s;s.resize(c[i].se);
		ref(j,0,SZ(c)-1)if(j!=i){
			int w=mi((c[j].fi-c[i].fi+p)%p,p-2);
			int ww=mi(p-w,c[j].se);
			ref(k,0,c[i].se-1){
				s[k]=mul(C[c[j].se+k-1][k],ww);
				ww=mul(ww,w);
			}
			if(ss.empty())ss=s;else ss=mul_poly(ss,s);
			ss.resize(c[i].se);
		}
		ref(j,0,c[i].se-1){
			s[j]=0;
			int w=p-c[i].fi,ww=1;
			ref(k,j,c[i].se-1){
				inc(s[j],mul(ss[k],mul(C[k][j],ww)));
				ww=mul(ww,w);
			}
		}
		//cout<<c[i].fi<<":";
		//ref(j,0,SZ(s)-1)cout<<s[j]<<" ";puts("");
		ref(j,0,SZ(c)-1)if(j!=i)
			ref(k,1,c[j].se){
				s.pb(0);
				for(int l=SZ(s)-1;l>=0;--l){
					int w=mul(s[l],c[j].fi);
					if(l)s[l]=s[l-1];else s[l]=0;
					dec(s[l],w);
				}
			}
		ref(j,0,SZ(s)-1)s[j]=mul(s[j],c[i].fi);
		//ref(j,0,SZ(s)-1)cout<<s[j]<<" ";puts("");
		res=add_poly(res,s);
	}
	mat ans=get_ans(res,A);
	ref(i,0,n-1){
		ref(j,0,n-1)cout<<ans.a[i][j]<<" ";
		cout<<endl;
	}
}
void work2(int n,mat A){
	vector<int> fx=A.minimal_poly();
	//vector<int> px=A.poly();
	//ref(i,0,SZ(fx)-1)cout<<fx[i]<<" ";puts("");
	//ref(i,0,SZ(mx)-1)cout<<mx[i]<<" ";puts("");
	vector<int> vx=div_poly(fx,gcd_poly(fx,dif_poly(fx)));
	//ref(i,0,SZ(vx)-1)cout<<vx[i]<<" ";puts("");
	vector<int> vtx=vx;
	vector<int> theta,vy,res;
	vy.pb(1);res.pb(0);res.pb(1);
	vector<int> nvx=inv_poly(dif_poly(vx),vx).fi;
	//printf("vx:");print(vx);
	//printf("res:");print(res);printf("vy:");print(vy);
	for(int ti=1;;vtx=mul_poly(vtx,vx),++ti){
		//printf("vx:");print(vx);
		//printf("%d---------\n",ti);
		vector<int> r=mod_poly(vtx,fx);
		if(SZ(r)==1&&r[0]==0)break;
		theta=mod_poly(mul_poly(mod_poly(vy,vx),nvx),vx);
		//printf("theta:");print(theta);
		//if(SZ(theta)==1&&theta[0]==0)continue;
		res=sub_poly(res,mul_poly(vtx,theta));
		vy=com_poly(vx,res);
		//printf("res:");print(res);printf("vy:");print(vy);
		//printf("vy mod vtx %d :",ti+1); print(mod_poly(vy,mul_poly(vx,vtx)));
		vy=div_poly(vy,mul_poly(vx,vtx));
	}
	res=mod_poly(res,fx);
	mat ans=get_ans(res,A);
	ref(i,0,n-1){
		ref(j,0,n-1)cout<<ans.a[i][j]<<" ";
		cout<<endl;
	}
}
int main(){
	int n;cin>>n>>p;mat A(n);
	ref(i,0,n*2)C[i][0]=1;
	ref(i,1,n*2)ref(j,1,i)C[i][j]=(C[i-1][j]+C[i-1][j-1])%p;
	ref(i,0,A.n-1)ref(j,0,A.n-1)cin>>A.a[i][j];
	if(p<=1000000)work1(n,A);else work2(n,A);
	//work2(n,A);
}