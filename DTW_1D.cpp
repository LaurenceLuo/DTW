// **************************************************************
// *
// *  Preproccessing.cpp
// *
// *  Based on LB_Keogh and LSH algorithm, perform fast Dynamic Time Wrapping
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
#include <random>
#include "RTree.h"
#include <queue>
#include <ctime>


using namespace std;


#define M 455 //The number of time series
#define T 270 //The length of a time serie
//#define D 20 //The dimension of a time point
#define bandwidth  0.02*T//Used for Sakoe-Chiba Band restriction, 0<=bandwidth<=T
#define slope_variance 1 //Used for Itakura parallelogram restriction
#define constraint 5 //Itakura parallelogram window, must be smaller than T
#define PAAReductionFactor 10 //the equal amount for each cell, must be a factor of T
#define L 4//The number of LSH function groups
#define K 5//The number of LSH functions in each group
#define W 1//Numerical constant
#define threshold 700
#define BlockNum T/PAAReductionFactor//The number of blocks left after using PAA
#define Epsilon 0.1*sqrt(T)//Threshold used in RTree RangeSearch


//compute Euclidean distance between two datasets with length N
float distance(float p[], float q[], int N)
{
	float dist = 0;
	for (int i = 0; i<N; i++)
	{
		dist += (p[i] - q[i])*(p[i] - q[i]);
	}
	return sqrt(dist);
}

//load dataset from files
float**  load_data(const char* filename, int row, int col)
{
	ifstream file(filename); // declare file stream:     
	string value;
	int i, j;
	int count = -1;
	string num;
	float **data = new float*[row];
	for (int i = 0; i < row; i++)
		data[i] = new float[col];

	while (file.good())
	{
		getline(file, value, ','); // read a string until next comma:  
		count += 1;
		i = count / (col);
		j = count % (col);
		//cout << string( value, 0, value.length() )<<",";  
		num = string(value, 0, value.length());
		if (count<row*col)
			data[i][j] = ::atof(num.c_str());
	}
	file.close();

	return data;
}


//normalize input datasets to the range of [0,1]
void normalization_1D(float**&p, int row, int col) 
{
	float max =  -INFINITY ;
	float min =  INFINITY ;
	int i, j;
	
	for (i = 0; i < row; i++){
		for (j = 0; j < col; j++){
			if (p[i][j] >= max)
				max = p[i][j];
			if (p[i][j] < min)
				min = p[i][j];
		}
	}
	
	for (i = 0; i < row; i++){
		for (j = 0; j < col; j++){
			if (max == min)
				p[i][j] = 0;
			else
			    p[i][j] = (p[i][j] - min) / (max - min);
		}
	}
}


//Basic one dimensional DTW
float DTW_Basic(float* p, float* q)
{
    float gamma[T][T];
    float dist[T][T];
    for(int i=0;i<T;i++){
        for(int j=0;j<T;j++){
            dist[i][j]=sqrt((p[i]-q[j])*(p[i]-q[j]));//distance(p[i],q[j]);
        }
    }
    gamma[0][0]=dist[0][0];
    for(int i=1;i<T;i++){
        gamma[0][i]=dist[0][i]+gamma[0][i-1];
        //gamma[0][i]=INFINITY;
    }
    for(int i=1;i<T;i++){
        gamma[i][0]=dist[i][0]+gamma[i-1][0];
        //gamma[i][0]=INFINITY;
    }
    for(int i=1;i<T;i++){
        for(int j=1;j<T;j++){
            if ((j - i < bandwidth) && (j - i > -bandwidth))//Rectangle restriction
                gamma[i][j]=min(gamma[i-1][j-1],min(gamma[i-1][j],gamma[i][j-1]))+dist[i][j];
            else gamma[i][j]=dist[i][j];
        }
    }
    //cout<<gamma[95][95]<<endl;
    vector<pair<int,int> > pair_vector;
    int i=0;
    int j=0;
    //int i=T-1;
    //int j=T-1;
    /*while(i>0&&j>0){
        if(i==0)
            j-=1;
        else if(j==0)
            i-=1;
        else{
            if(gamma[i-1][j]==min(gamma[i-1][j-1],min(gamma[i-1][j],gamma[i][j-1])))
             i=i-1;
             else if(gamma[i][j-1]==min(gamma[i-1][j-1],min(gamma[i-1][j],gamma[i][j-1])))
             j=j-1;

            //if(gamma[i][j]-dist[i][j]==gamma[i-1][j])
                //i=i-1;
            //else if(gamma[i][j]-dist[i][j]==gamma[i][j-1])
                //j=j-1;
            else{
                i-=1;
                j-=1;
            }
        }
        //pair_vector.push_back(make_pair(i,j));
        pair_vector.push_back(make_pair(i,j));
    }*/
    while(i<T-1&&j<T-1){
        if(i==T-2&&j!=T-2)
            j+=1;
        else if(j==T-2&&i!=T-2)
            i+=1;
        else if(i==T-2&&i==T-2){
            i+=1;
            j+=1;
        }
        else{
            if(gamma[i+1][j+1]-dist[i+1][j+1]==gamma[i+1][j])
             i+=1;
             else if(gamma[i+1][j+1]-dist[i+1][j+1]==gamma[i][j+1])
             j+=1;
            else{
                i+=1;
                j+=1;
            }
        }
        //pair_vector.push_back(make_pair(i,j));
        pair_vector.push_back(make_pair(i,j));
    }
    //cout<<"(p, q)"<<endl;
    float cost=0;
    for(int i=0;i<pair_vector.size();i++){
        //cout << "Pair: "<<pair_vector[i].first << ", " << pair_vector[i].second << endl;
        cost=cost+(p[pair_vector[i].first]-q[pair_vector[i].second])*(p[pair_vector[i].first]-q[pair_vector[i].second]);
        //cout<<cost<<endl;
    }
    //cout<<"Cost calculated using pairs: "<<sqrt(cost)<<endl;
    //return sqrt(gamma[T-1][T-1]);
    //cout<<"Cost calculated using gamma: "<<sqrt(gamma[T-1][T-1])<<endl;
    /*cout<<"Cost calculated using gamma: "<<sqrt(gamma[T-1][T-2])<<endl;
    cout<<"Cost calculated using gamma: "<<sqrt(gamma[T-2][T-1])<<endl;
    cout<<"Cost calculated using gamma: "<<sqrt(gamma[T-2][T-2])<<endl;
    cout<<"Cost calculated using gamma: "<<sqrt(gamma[T-1][T-3])<<endl;
    cout<<"Cost calculated using gamma: "<<sqrt(gamma[T-3][T-1])<<endl;*/
    return sqrt(cost);

}


// Compute one dimensional PAA Upper Bound
float* computePAAUpper_1D(float* p){
    float* temp=new float[T];
    float* upper=new float[BlockNum];
        /*int count=0;
        for(int i=0;i<T;i++){
            float largest_temp=p[i];
            if(i<constraint){
                for(int j=0;j<i+count+1;j++){
                    if(p[j]>=largest_temp)
                        largest_temp=p[j];
                }
                count++;
            }
            else if(i<T-constraint){
                for(int j=i-constraint;j<i+constraint+1;j++){
                    if(p[j]>=largest_temp)
                        largest_temp=p[j];
                }
            }
            else{
                for(int j=i-count+1;j<T;j++){
                    if(p[j]>=largest_temp)
                        largest_temp=p[j];
                }
                count--;
            }
            upper[i]=largest_temp;
        }//build Itakura parallelogram envelope*/
    for(int i=0;i<T;i++){
        float largest_temp=p[i];
        if(i<constraint){
            for(int j=0;j<i+constraint+1;j++){
                if(p[j]>=largest_temp)
                    largest_temp=p[j];
            }
        }
        else if(i<T-constraint){
            for(int j=i-constraint;j<i+constraint+1;j++){
                if(p[j]>=largest_temp)
                    largest_temp=p[j];
            }
        }
        else{
            for(int j=i-constraint;j<T;j++){
                if(p[j]>=largest_temp)
                    largest_temp=p[j];
            }
        }
        temp[i]=largest_temp;
    }//build Sakoe-Chiba band envelope*/

    for(int i=0;i<T;i=i+PAAReductionFactor){
        float largest_temp=temp[i];
        for(int j=i;j<i+PAAReductionFactor;j++){
            if(temp[j]>=largest_temp)
                largest_temp=temp[j];
        }
        upper[i/PAAReductionFactor]=largest_temp;
    }//Apply PAA
    delete[] temp;
    return upper;
}

// Compute one dimensional PAA Lower Bound
float* computePAALower_1D(float* p){
    float*temp=new float[T];
    float* lower=new float[BlockNum];
    /*int count=0;
    for(int i=0;i<T;i++){
        float smallest_temp=p[i];
        if(i<constraint){
            for(int j=0;j<i+count+1;j++){
                if(p[j]<=smallest_temp)
                    smallest_temp=p[j];
            }
            count++;
        }
        else if(i<T-constraint){
            for(int j=i-constraint;j<i+constraint+1;j++){
                if(p[j]<=smallest_temp)
                    smallest_temp=p[j];
            }
        }
        else{
            for(int j=i-count+1;j<T;j++){
                if(p[j]<=smallest_temp)
                    smallest_temp=p[j];
            }
            count--;
        }
        lower[i]=smallest_temp;
    }//build Itakura parallelogram envelope*/
    for(int i=0;i<T;i++){
        float smallest_temp=p[i];
        if(i<constraint){
            for(int j=0;j<i+constraint+1;j++){
                if(p[j]<=smallest_temp)
                    smallest_temp=p[j];
            }
        }
        else if(i<T-constraint){
            for(int j=i-constraint;j<i+constraint+1;j++){
                if(p[j]<=smallest_temp)
                    smallest_temp=p[j];
            }
        }
        else{
            for(int j=i-constraint;j<T;j++){
                if(p[j]<=smallest_temp)
                    smallest_temp=p[j];
            }
        }
        temp[i]=smallest_temp;
    }//build Itakura parallelogram envelope
    for(int i=0;i<T;i=i+PAAReductionFactor){
        float smallest_temp=temp[i];
        for(int j=i;j<i+PAAReductionFactor;j++){
            if(temp[j]<=smallest_temp)
                smallest_temp=temp[j];
        }
        lower[i/PAAReductionFactor]=smallest_temp;
    }//Apply PAA
    delete[] temp;
    return lower;
}

// Compute LB_PAA distance based on previous computed PAA Upper Bound and Lower Bound
float compute_LB_PAA_1D(float* standard, float* q){
    float* upperBound=computePAAUpper_1D(standard);
    float* lowerBound=computePAALower_1D(standard);
    
    float* q_PAA=new float[BlockNum];
    for(int i=0;i<T;i=i+PAAReductionFactor){
        float sum_temp=0;
        for(int j=i;j<i+PAAReductionFactor;j++){
            sum_temp+=q[j];
        }
        q_PAA[i/PAAReductionFactor]=sum_temp/PAAReductionFactor;
    }
    
    float LB_PAA=0;
    for(int i=0;i<BlockNum;i++){
        if(q_PAA[i]>upperBound[i])
            LB_PAA+=(q_PAA[i]-upperBound[i])*(q_PAA[i]-upperBound[i]);
        else if(q_PAA[i]<lowerBound[i])
            LB_PAA+=(q_PAA[i]-lowerBound[i])*(q_PAA[i]-lowerBound[i]);
    }
    delete[] upperBound;
    delete[] lowerBound;
    delete[] q_PAA;
    return sqrt(PAAReductionFactor*LB_PAA);
}

float MINDIST(float* query_series, RTree::Rect MBR){
    float dist=0;
    float* upperBound=computePAAUpper_1D(query_series);
    float* lowerBound=computePAALower_1D(query_series);
    for(int i=0;i<BlockNum;i++){
        if(lowerBound[i]>MBR.m_max[i])
            dist+=(lowerBound[i]-MBR.m_max[i])*(lowerBound[i]-MBR.m_max[i]);
        else if(upperBound[i]<MBR.m_min[i])
            dist+=(upperBound[i]-MBR.m_min[i])*(upperBound[i]-MBR.m_min[i]);
    }
    dist=T*dist/BlockNum;
    
    delete[] upperBound;
    delete[] lowerBound;
    //cout<<"MINDIST :"<<sqrt(dist)<<endl;
    return sqrt(dist);
}
vector<int> RangeSearch(float* series, float bound, RTree::Node* current, vector<int>& candidate, float** standard){
    if(!current->IsLeaf()){
        for(int i=0;i<current->m_count;i++){
            if(MINDIST(series, current->m_branch[i].m_rect)<=bound){
                RangeSearch(series, bound, current->m_branch[i].m_child,candidate,standard);
            }
        }
    }
    else{
        for(int i=0;i<current->m_count;i++){
            if(compute_LB_PAA_1D(series,standard[current->m_branch[i].m_data])<=bound)
                if(DTW_Basic(series,standard[current->m_branch[i].m_data])<=bound)
                    candidate.push_back(current->m_branch[i].m_data);
        }
    }
    return candidate;
}
vector<int> RangeSearch(float* series, float bound, RTree::Node* root, float** standard){
    vector<int> candidate;
    return RangeSearch(series, bound, root, candidate,standard);
}



int main(){
	float **dataset=load_data("./dataset.txt", M, T);
	normalization_1D(dataset, M, T);
    
    //some testing:
    /*float *temp=new float[T];
    temp[0]=0;
    temp[1]=0;
    for(int i=2;i<T;i++){
        temp[i]=dataset[0][i-1];
        //cout<<temp[i]<<endl;
    }
    for(int i=0;i<T;i++){
    cout<<dataset[2][i]<<endl;
    }
    cout<<"DTW: "<<DTW_Basic(temp,dataset[0])<<endl;
    cout<<"Euclean: "<<distance(temp, dataset[0], T)<<endl;
    delete[] temp;*/
    cout<<"Testing: "<<endl;
    cout<<"LB_PAA: "<<compute_LB_PAA_1D(dataset[1],dataset[2])<<endl;
    cout<<"DTW: "<<DTW_Basic(dataset[1],dataset[2])<<endl;
    cout<<"Euclean: "<<distance(dataset[1], dataset[2], T)<<endl;
    
    
    
    /*Ground Truth*/
    cout<<"Ground Truth: "<<endl;
    clock_t begin = clock();
    int count=0;
    for(int i=1;i<M;i++){
        if(DTW_Basic(dataset[0],dataset[i])<=Epsilon){
            cout<<"Candidate series number by pure DTW: "<<i<<endl;
            count++;
        }
    }
    cout<<"The total number of candidate series for ground truth: "<<count<<endl;
    clock_t end = clock();
    double elapsed_secs = double(end - begin) / CLOCKS_PER_SEC;
    cout<<"The time spent for ground truth: "<< elapsed_secs<<" seconds."<<endl;
    cout<<"/****************************************************************************/"<<endl;
    /*Ground Truth*/
    
    
    
    /*DTW using LB_PAA RTree indexing*/
    cout<<"RTree indexing: "<<endl;
    float** upperMBR=new float *[M];
    float** lowerMBR=new float *[M];
    for(int i=0;i<M;i++){
        upperMBR[i]=computePAAUpper_1D(dataset[i]);
        lowerMBR[i]=computePAALower_1D(dataset[i]);
    }
    RTree MyTree;
    for(int m=0;m<M;m++){
        MyTree.Insert(upperMBR[m], lowerMBR[m], m);
    }
    //cout<<"!!!!"<<(*MyTree.m_root).m_branch[0].m_rect.m_max[0]<<endl;
    //cout<<"!!!!"<<(*MyTree.m_root).m_branch[0].m_rect.m_min[0]<<endl;
    //up to here is building the tree
    clock_t begin2=clock();
    vector<int> candidate=RangeSearch(dataset[0],Epsilon,MyTree.m_root,dataset);
    int count_PAA=0;
    for(vector<int>::iterator it=candidate.begin();it!=candidate.end();++it){
        cout<<"Candidate series number by LB_PAA RTree indexing: "<<(*it)<<endl;
        count_PAA++;
    }
    cout<<"The total number of candidate series for indexing: "<<count_PAA<<endl;
    clock_t end2 = clock();
    double elapsed_secs2 = double(end2 - begin2) / CLOCKS_PER_SEC;
    cout<<"The time spent for RTree range searching: "<< elapsed_secs2<<" seconds."<<endl;
    /*DTW using LB_PAA RTree indexing*/
    
    for(int i=0;i<M;i++){
        delete []dataset[i];
        delete []upperMBR[i];
        delete []lowerMBR[i];
    }
    delete []upperMBR;
    delete []lowerMBR;
    delete[] dataset;
    return 0;
}

