// **************************************************************
// *		   
// *  DTW.cpp
// *		   
// *  Given two large dataset, perform Dynamic Time Wrapping technic
// *		   
// **************************************************************
#include <stdio.h>
#include <cstdlib>
#include <math.h>
#include <time.h>
#include <iostream>
#include <string>
#include <sstream>
#include <fstream>
#include <vector>
#include <list>
#include <algorithm>
#include <cstdlib>
#include <utility>

#define m 50 //boundary for the first dataset P
#define n 50 //boundary for the second dataset Q
#define constraint 10
#define bandwidth 10


using namespace std;

//compute Euclidean distance between two points
float distance(float x, float y)
{
    return sqrt((x-y)*(x-y));
    
}

/* Load data in one dimension
 */
float* load_data(const char* filename, int length){
    ifstream file(filename); // declare file stream:
    string value;
    string num;
    int count=0;
    float* data = new float[length];
    while (file.good())
    {
        getline(file, value, ','); // read a string until next comma:
        num = string(value, 0, value.length());
        if (count<length)
            data[count] = ::atof(num.c_str());
        count += 1;
    }
    file.close();
    return data;
    
}

float DTW(float* p, float* q){
    float best=10000.0;
    float gamma[m][n];
    for(int i=0;i<m;i++){
        for(int j=0;j<n;j++){
            gamma[i][j]=best;
        }
    }
    for(int i=0;i<m;i++){
        for(int j=0;j<n;j++){
            if(((m/n)*j-i<=constraint)&&((m/n)*j-i>=-constraint)){//Rectangle restriction
            //for(int j=max(0,j-constraint);j<min(n,i+constraint+1);j++){
                if(i > 0)
                    best = gamma[i - 1][j];
                if(j > 0)
                    best = min(best, gamma[i][j - 1]);
                if((i > 0) && (j > 0))
                    best = min(best, gamma[i - 1][j - 1]);
                if((i == 0) && (j == 0))
                    gamma[i][j] = distance(p[i],q[j]);//v[i].euclid_distance(w[j]);
                else
                    gamma[i][j] = best + distance(p[i],q[j]);//v[i].euclid_distance(w[j]);
            //cout<<dist[i][j]<<", ";
            }
        }
    }
    
    vector<pair<int,int> > pair_vector;
    int i=m-1;
    int j=n-1;
    while(i>0&&j>0){
        if(i==0)
            j-=1;
        else if(j==0)
            i-=1;
        else{
            if(gamma[i-1][j]==min(gamma[i-1][j-1],min(gamma[i-1][j],gamma[i][j-1])))
                i=i-1;
            else if(gamma[i][j-1]==min(gamma[i-1][j-1],min(gamma[i-1][j],gamma[i][j-1])))
                j=j-1;
            else {
                i-=1;
                j-=1;
            }
        }
        pair_vector.push_back(make_pair(j,i));
    }
    pair_vector.push_back(make_pair(0,0));
    cout<<"(p, q)"<<endl;
    for(int i = 0; i < pair_vector.size(); i++)
    {
        cout << pair_vector[i].second << ", " << pair_vector[i].first << endl;
    }
    float cost=0;
    for(int i=0;i<pair_vector.size();i++){
        //cout<<p[pair_vector[i].first]<<", "<<q[pair_vector[i].second]<<endl;
        cost=cost+distance(p[pair_vector[i].second],q[pair_vector[i].first]);
    }
    cout<<gamma[m-2][n-2]<<endl;
    cout<<gamma[m-1][n-1]<<endl;
    return cost;//cost only considers pairs we get
}

int main(int argc, char* argv[]){
    float* datasetQ=load_data("./datasetQ.txt",n);
    float* datasetP=load_data("./datasetP.txt",m);
    
    /*float* datasetP=new float[10];
    datasetP[0]=1;
    datasetP[1]=1;
    datasetP[2]=2;
    datasetP[3]=3;
    datasetP[4]=2;
    datasetP[5]=0;
    float* datasetQ=new float[10];
    datasetQ[0]=0;
    datasetQ[1]=1;
    datasetQ[2]=1;
    datasetQ[3]=2;
    datasetQ[4]=3;
    datasetQ[5]=2;
    datasetQ[6]=1;*/
    
    cout<<DTW(datasetP,datasetQ);
    
    delete[] datasetQ;
    delete[] datasetP;
    return 0;
        
}
