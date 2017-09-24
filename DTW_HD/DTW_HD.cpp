// DTW.cpp : Defines the entry point for the console application.
//

//#include "stdafx.h"
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
//#include "RTree_HD.h"
#include <queue>
#include <ctime>
#include <iterator>


using namespace std;


#define M 4000 //The number of time series
#define T 256 //The length of a time serie 256
#define D 64 //The dimension of a time point
#define bandwidth  0.12*T//Used for Sakoe-Chiba Band restriction, 0<=bandwidth<=T
//#define slope_variance 1 //Used for Itakura parallelogram restriction
#define constraint 4 //Itakura parallelogram window, must be smaller than T
#define PAAReductionFactor 1//the equal amount for each cell, must be a factor of T
#define L 3//The number of LSH function groups
#define K 6//The number of LSH functions in each group
#define W 1//Numerical constant
#define threshold 120//410
#define BlockNum T/PAAReductionFactor//The number of blocks left after using PAA
#define Epsilon 0.03*sqrt(D)*sqrt(T)//Threshold used in RTree RangeSearch
#define R 0.5*sqrt(D)
#define KNN 50
#define FLAG 50
#define LSHfunc 200
#define NUM 0.1*M
#define ratio 0.99
#define SD 0.01
#define ClusterNum 2

//Parameters for SSH contrast experiment
#define Delta 4 //Step Size
#define Size_W 16 //Vector Size
#define NB (T-Size_W)/Delta //Stream Size
#define N_grams 4 //The number of grams
#define Length_N pow(2,N_grams) //The length of each of the n grams
#define HashtableNum 20 //The number of hash tables


// r=0.04   t=140
// r=0.06   t=108

// T=128
// T=512



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

//compute Euclidean distance between two points with dimension d
float distance_HD(float p[], float q[], int d)
{
	float dist = 0;
	for (int i = 0; i<d; i++) {
		dist += (p[i] - q[i])*(p[i] - q[i]);
	}
	return dist;
}


//compute Euclidean distance between two points with dimension d
float Euclidean_disatance(float p[], float q[], int d)
{
	float dist = 0;
	for (int i = 0; i<d; i++) {
		dist += (p[i] - q[i])*(p[i] - q[i]);
	}
	return sqrt(dist);
}


//compute Euclidean distance between two series with dimension d
float distance_HD(float** p, float** q)
{
	float dist = 0;
	for (int i = 0; i<T; i++) {
		for (int j = 0; j<D; j++) {
			dist += (p[i][j] - q[i][j])*(p[i][j] - q[i][j]);
		}
	}
	return sqrt(dist);
}

//load dataset from files
float**  load_data(const char* filename, int row, int col)
{
	ifstream file(filename); // declare file stream:
	string value;
	string num;
	int i, j;
	int count = -1;
	float **data = new float*[row];
	for (int i = 0; i < row; i++)
		data[i] = new float[col+1];

	for (int i = 0; i<row; i++) {
		for (int j = 0; j<col; j++) {
			getline(file, value, ' ');
			num = string(value, 0, value.length());
			data[i][j] = ::atof(num.c_str());
		}
        getline(file,value);
        num = string(value);
        data[i][col]= atof(value.c_str());
	}
	file.close();
	return data;
}

//normalize input datasets to the range of [0,1]
void normalization_HD(float***&p) {
	float max[D] = { -INFINITY };
	float min[D] = { INFINITY };

	for (int d = 0; d<D; d++) {
		for (int i = 0; i<M; i++) {
			for (int j = 0; j<T; j++) {
				if (p[i][j][d] >= max[d])
					max[d] = p[i][j][d];
				if (p[i][j][d]<min[d])
					min[d] = p[i][j][d];
			}
		}
	}
	for (int i = 0; i<M; i++) {
		for (int j = 0; j<T; j++) {
			for (int d = 0; d<D; d++) {
				p[i][j][d] = 2*(p[i][j][d] - min[d]) / (max[d] - min[d])-1;
			}
		}
	}

}


//Basic one dimensional DTW
float DTW_Basic(float* p, float* q)
{
	float gamma[T][T];
	float dist[T][T];
	for (int i = 0; i<T; i++) {
		for (int j = 0; j<T; j++) {
			dist[i][j] = (p[i] - q[j])*(p[i] - q[j]);//distance(p[i],q[j]);
		}
	}
	gamma[0][0] = dist[0][0];
	for (int i = 1; i<T; i++) {
		gamma[0][i] = dist[0][i] + gamma[0][i - 1];
		//gamma[0][i]=INFINITY;
	}
	for (int i = 1; i<T; i++) {
		gamma[i][0] = dist[i][0] + gamma[i - 1][0];
		//gamma[i][0]=INFINITY;
	}
	for (int i = 1; i<T; i++) {
		for (int j = 1; j<T; j++) {
			if ((j - i < bandwidth) && (j - i > -bandwidth))//Rectangle restriction
				gamma[i][j] = min(gamma[i - 1][j - 1], min(gamma[i - 1][j], gamma[i][j - 1])) + dist[i][j];
			else gamma[i][j] = dist[i][j];
		}
	}

	//cout<<gamma[95][95]<<endl;
	vector<pair<int, int> > pair_vector;
	int i = 0;
	int j = 0;

	while (i<T - 1 && j<T - 1) {
		if (i == T - 2 && j != T - 2)
			j += 1;
		else if (j == T - 2 && i != T - 2)
			i += 1;
		else if (i == T - 2 && i == T - 2) {
			i += 1;
			j += 1;
		}
		else {
			if (gamma[i + 1][j + 1] - dist[i + 1][j + 1] == gamma[i + 1][j])
				i += 1;
			else if (gamma[i + 1][j + 1] - dist[i + 1][j + 1] == gamma[i][j + 1])
				j += 1;
			else {
				i += 1;
				j += 1;
			}
		}
		pair_vector.push_back(make_pair(i, j));
	}
	//cout<<"(p, q)"<<endl;
	float cost = 0;
	for (int i = 0; i<pair_vector.size(); i++) {
		//cout << "Pair: "<<pair_vector[i].first << ", " << pair_vector[i].second << endl;
		cost = cost + (p[pair_vector[i].first] - q[pair_vector[i].second])*(p[pair_vector[i].first] - q[pair_vector[i].second]);
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




//Multi-dimension DTW by calculating DTW in every dimension and sum them up, using DTW_Basic function
float DTW_1D(float** p, float** q) {
	float gamma[D][D];
	float dist[D][D];
	float** p_new = new float*[D];
	float** q_new = new float*[D];
	for (int i = 0; i < D; i++) {
		p_new[i] = new float[T];
		q_new[i] = new float[T];
	}
	for (int i = 0; i<D; i++) {
		for (int j = 0; j<T; j++) {
			p_new[i][j] = p[j][i];
			q_new[i][j] = q[j][i];
		}
	}
	float cost = 0;
	for (int i = 0; i<D; i++) {
		cost += DTW_Basic(p_new[i], q_new[i]);
	}


	for (int i = 0; i < D; i++) {
		delete[] p_new[i];
		delete[] q_new[i];
	}
	delete[] p_new;
	delete[] q_new;

	return cost;//square root? Already did in DTW_Basic
}


//Basic multiple dimensional DTW
float DTW_HD(float** p, float** q)
{
	float gamma[T][T];
	float dist[T][T];
	for (int i = 0; i<T; i++) {
		for (int j = 0; j<T; j++) {
			dist[i][j] = distance_HD(p[i], q[j], D); //no sqrt
		}
	}
	gamma[0][0] = dist[0][0];
	for (int i = 1; i<T; i++) {
		gamma[0][i] = dist[0][i] + gamma[0][i - 1];
		gamma[i][0] = dist[i][0] + gamma[i - 1][0];
		//gamma[i][0]=INFINITY;
	}
	float temp = 0;
	for (int i = 1; i<T; i++) {
		for (int j = 1; j<T; j++) {
			if ((j - i < bandwidth) && (j - i > -bandwidth))//Rectangle restriction
				gamma[i][j] = min(gamma[i - 1][j - 1], min(gamma[i - 1][j], gamma[i][j - 1])) + dist[i][j];
			else gamma[i][j] = dist[i][j];
			if (gamma[i][j] >= temp) {
				temp = gamma[i][j];
			}
		}
	}
	//cout<<gamma[95][95]<<endl;
	vector<pair<int, int> > pair_vector;
	int i = 0;
	int j = 0;
	while (i<T - 1 && j<T - 1) {
		if (i == T - 2 && j != T - 2)
			j += 1;
		else if (j == T - 2 && i != T - 2)
			i += 1;
		else if (i == T - 2 && i == T - 2) {
			i += 1;
			j += 1;
		}
		else {
			if (gamma[i + 1][j + 1] - dist[i + 1][j + 1] == gamma[i + 1][j])
				i += 1;
			else if (gamma[i + 1][j + 1] - dist[i + 1][j + 1] == gamma[i][j + 1])
				j += 1;
			else {
				i += 1;
				j += 1;
			}
		}
		//pair_vector.push_back(make_pair(i,j));
		pair_vector.push_back(make_pair(i, j));
	}
	float cost = 0;
	for (int i = 0; i<pair_vector.size(); i++) {
		//cout << "Pair: "<<pair_vector[i].first << ", " << pair_vector[i].second << endl;
		cost = cost + distance_HD(p[pair_vector[i].first], q[pair_vector[i].second], D);
	}
	return sqrt(cost);
}

vector<int> DTW_GroundTruth_Range(float**query, float*** datasets) {
// find series which DTW<value and fall in the r-envelop of query series
	vector<int >candidate;
	float dtw_dist = 0;
	for (int i = 0; i<M; i++) {
		dtw_dist = DTW_HD(query, datasets[i]);
		if (dtw_dist <= Epsilon) 
		{
			bool isTrue = true;
			for (int j = 0; j<T; j++)
			{
				if (Euclidean_disatance(query[j], datasets[i][j], D)> R)
				{
					isTrue = false;
					break;
				}			
			}
			if (isTrue)			
			candidate.push_back(i);
		}
	}
	return candidate;
}

vector<int> DTW_GroundTruth_KNN(float** query, float*** datasets){
    struct sort_int_StoL {
        bool operator()(int left, int right) {
            return left < right;
        }
    };//Int from small to large
    vector<pair<int,float> > candidate_KNN;
    int count=0;
    struct sort_pred {
        bool operator()(const std::pair<int,float> &left, const std::pair<int,float> &right) {
            return left.second < right.second;
        }
    };
    for(int m=0;m<M;m++){
        if(count<KNN){
            candidate_KNN.push_back(make_pair(m,DTW_HD(query,datasets[m])));
        }
        else{
            sort(candidate_KNN.begin(),candidate_KNN.end(),sort_pred());
            float temp=DTW_HD(query,datasets[m]);
            if(temp<candidate_KNN.back().second){
                candidate_KNN.pop_back();
                candidate_KNN.push_back(make_pair(m,temp));
            }
        }
        count++;
    }
    vector<int> KNN_output;
    for(vector<pair<int,float> >::iterator it=candidate_KNN.begin();it!=candidate_KNN.end();++it){
        KNN_output.push_back((*it).first);
    }
    sort(KNN_output.begin(), KNN_output.end(), sort_int_StoL());
    return KNN_output;
}


float**** generateRandom() {
	default_random_engine generator(time(NULL));
	normal_distribution<float> distribution(0.0, 1.0);
	float ****random;
	random = new float ***[L];
	for (int l = 0; l<L; l++) {
		random[l] = new float **[K];
                for (int k = 0; k<K; k++) {
			random[l][k] = new float*[LSHfunc];		
		        for (int t = 0; t<LSHfunc; t++) {
			     random[l][k][t] = new float[D];
			}
		}
	}
	for (int l = 0; l < L; l++) {
		for (int k = 0; k < K; k++) {
			for (int t = 0; t<LSHfunc; t++) {
				for (int d = 0; d<D; d++) {
					float temp = distribution(generator);;
					while (temp<0 || temp>1)
						temp = distribution(generator);
					random[l][k][t][d] = temp;
 				}
			}	
		}
	}
	return random;
}



//compute LSH-PAA-datsets for all datasets.
float ***compute_LSH_PAA_datasets(float***& p)
{
	float ***PAA_datasets;
	int m, l, d, t;
	float value;
	PAA_datasets = new float**[M];
	for ( m = 0; m<M; m++)
	{
		PAA_datasets[m] = new float*[BlockNum];
		for ( l = 0; l<BlockNum; l++) 
		{
			PAA_datasets[m][l] = new float[D];
		}
	}
	for (m = 0; m < M; m++)
	{
		for (l = 0; l < BlockNum; l++)
		{
			for (d = 0; d < D; d++)
			{
				value = 0;
				for (t = 0; t < PAAReductionFactor; t++)
				{
					value += p[m][l*PAAReductionFactor + t][d];
				}
				PAA_datasets[m][l][d] = value / PAAReductionFactor;
			}
		}
	}
	return PAA_datasets;
}



//Calculate LSH for the whole datasets(PAA)
float **** CalculateLSH(float*** p, float**** random) {
	float ****hash_value;
	hash_value = new float***[M];
	for (int m = 0; m<M; m++) {
		hash_value[m] = new float**[L];
		for (int l = 0; l<L; l++) {
			hash_value[m][l] = new float*[K];
			for (int k = 0; k<K; k++) {
				hash_value[m][l][k] = new float[BlockNum];
			}
		}
	}
	for (int m = 0; m<M; m++) {
		for (int l = 0; l<L; l++) 
		{
			for (int k = 0; k<K; k++) 
			{
				for (int n = 0; n< BlockNum; n++)
				{
					float temp = 0;
					for (int d = 0; d<D; d++)
					{
						int tt=n%LSHfunc;
						temp += p[m][n][d] * random[l][k][tt][d];
					}
					hash_value[m][l][k][n] = floor(temp / W);
				}
			}
		}
	}
	return hash_value;
}

//Calculate LSH for one dataset(PAA)
float *** CalculateLSH(float** p, float**** random) {
	float ***hash_value;
	hash_value = new float**[L];
	for (int l = 0; l<L; l++) {
		hash_value[l] = new float*[K];
		for (int k = 0; k<K; k++) {
			hash_value[l][k] = new float[BlockNum];
		}
	}


	for (int l = 0; l<L; l++) {
		for (int k = 0; k<K; k++) {
			for (int n = 0; n<BlockNum; n++) {
				float temp = 0;
				for (int d = 0; d<D; d++) {
					int tt=n%LSHfunc;
					temp += p[n][d] * random[l][k][tt][d];
				}
				hash_value[l][k][n] = floor(temp / W);
			}
		}
	}
	return hash_value;
}



vector<int> REnvelope_GroundTruth(float** query, float*** datasets) {
	vector<int> candidate;
	for (int m = 0; m<M; m++)
	{
		bool isTrue = true;
		for (int i = 0; i<T; i++)
		{
			if (Euclidean_disatance(query[i], datasets[m][i], D)> R)
			{
				isTrue = false;
				break;
			}			
		}
		if (isTrue)
			candidate.push_back(m);
	}
	return candidate;
}


vector<int> LSH_query(float** query_paa, float**** hash_functions, float**** hash_value_paa) {
	float ***query_hash = CalculateLSH(query_paa, hash_functions);//query_hash[L][K][BlockNum], hashed values for the query series

	vector<int> candidate;
	for (int m = 0; m<M; m++)
	{
		for (int l = 0; l<L; l++) 
		{
			bool collision = true;
			for (int k = 0; k<K; k++) 
			{
				int count = 0;
				for (int n = 0; n<BlockNum; n++)
				{
					if (hash_value_paa[m][l][k][n] == query_hash[l][k][n]) 
					{
						count++;
					}
					if (count >= threshold) {
						break;
					}
				}
				if (count<threshold) {
					collision = false;
					break;
				}
			}
			if (collision == true) {
				candidate.push_back(m);
				break;
			}
		}
	}

	for (int l = 0; l<L; l++) {
		for (int k = 0; k<K; k++) {
			delete[]query_hash[l][k];
		}
		delete[]query_hash[l];
	}
	delete[]query_hash;

	return candidate;
}

vector<int>  LSH_KNN(vector<int> candidate, float** query, float*** datasets) {
	int count = 0;
	struct sort_pred {
		bool operator()(const std::pair<int, float> &left, const std::pair<int, float> &right) {
			return left.second < right.second;
		}
	};
	vector<pair<int, float> > candidate_KNN;
	for (vector<int>::iterator it = candidate.begin(); it != candidate.end(); ++it) {
		if (count<KNN) {
			candidate_KNN.push_back(make_pair((*it), DTW_HD(query, datasets[*it])));
			sort(candidate_KNN.begin(), candidate_KNN.end(), sort_pred());
		}
		else {
			sort(candidate_KNN.begin(), candidate_KNN.end(), sort_pred());
			float temp = DTW_HD(query, datasets[*it]);
			if (temp<candidate_KNN.back().second) {
				candidate_KNN.pop_back();
				candidate_KNN.push_back(make_pair((*it), temp));
			}
		}
		count++;
	}
	vector<int> KNN_output;
	for (vector<pair<int, float> >::iterator it = candidate_KNN.begin(); it != candidate_KNN.end(); ++it) {
		KNN_output.push_back((*it).first);
		//cout<<(*it).second<<endl;
	}

	return  KNN_output;

}



vector<int>  LSH_range_NN(vector<int> candidate, float** query, float*** datasets) {
	vector<int > range_NN;
	float dtw_dist = 0;
	for (vector<int>::iterator it = candidate.begin(); it != candidate.end(); ++it)
	{
		dtw_dist = DTW_HD(query, datasets[*it]);
		if (dtw_dist <= Epsilon) 
			range_NN.push_back(*it);
	}
	
	return range_NN;
}



vector<int>  LSH_LB_Pruning_range(vector<int> candidate, float**** hash_functions, float**** hash_value, float** query_paa, int query_id, float*** datasets) {
	struct sort_pred {
		bool operator()(const std::pair<int, float> &left, const std::pair<int, float> &right) {
			return left.second < right.second;
		}
	};//from small to large
	float ***query_hash = CalculateLSH(query_paa, hash_functions);
	vector<pair<int, float> > lower_bound;
	for (vector<int>::iterator it = candidate.begin(); it != candidate.end(); ++it) {
		float temp=0;
		float temp_series;
		for (int l = 0; l<L; l++)
		{
			for (int k = 0; k<K; k++) 
			{
				temp_series=0;
				for (int t = 0; t<BlockNum; t++) 
				{
					temp_series+= PAAReductionFactor*(query_hash[l][k][t] - hash_value[*it][l][k][t])*(query_hash[l][k][t] - hash_value[*it][l][k][t])*R*R;
				}
				temp+=sqrt(temp_series);
			}			
		}
		lower_bound.push_back(make_pair((*it), temp));
	}
	sort(lower_bound.begin(), lower_bound.end(), sort_pred());




	vector<int > range_NN;
	int flag = 0;
	int DTW_count = 0;
	float dtw_dist=0;
	for (vector<pair<int, float> >::iterator it = lower_bound.begin(); it != lower_bound.end(); ++it) 
	{
		dtw_dist = DTW_HD(datasets[query_id], datasets[(*it).first]);
		DTW_count++;
		if (dtw_dist <= Epsilon) 
		{
			range_NN.push_back((*it).first);
			flag=0;
		}
		else flag++;
		if (flag == FLAG)
			break;
	}
		
			
	for (int l = 0; l<L; l++) {
		for (int k = 0; k<K; k++) {
			delete[]query_hash[l][k];
		}
		delete[]query_hash[l];
	}
	delete[]query_hash;

	cout << "the number of DTW computation is " << DTW_count << endl;

	return range_NN;

}

vector<int> LSH_Intersection_Pruning_range(vector<int> candidate, float**** hash_functions, float**** hash_value, float** query_paa, int query_id, float*** datasets) {
	struct sort_LtoS {
		bool operator()(const std::pair<int, float> &left, const std::pair<int, float> &right) {
			return left.second > right.second;
		}
	};//from large to small
	struct sort_StoL {
		bool operator()(const std::pair<int, float> &left, const std::pair<int, float> &right) {
			return left.second < right.second;
		}
	};//from small to large
	float ***query_hash = CalculateLSH(query_paa, hash_functions);

	vector<pair<int, float> > Pro_sim;
	for (vector<int>::iterator it = candidate.begin(); it != candidate.end(); ++it) {
		float lower_temp = 0;
		float upper_temp = 0;
		float lower_temp_series, upper_temp_series;
		for (int l = 0; l<L; l++) 
		{
			for (int k = 0; k<K; k++) 
			{		
				lower_temp_series=0;
				upper_temp_series=0;
				for (int t = 0; t<BlockNum; t++)
				{
					lower_temp_series += PAAReductionFactor*(query_hash[l][k][t] - hash_value[*it][l][k][t])*(query_hash[l][k][t] - hash_value[*it][l][k][t])*R*R;
					upper_temp_series += PAAReductionFactor*(abs(query_hash[l][k][t] - hash_value[*it][l][k][t]) + 1)*(abs(query_hash[l][k][t] - hash_value[*it][l][k][t]) + 1)*R*R;
				}	
				lower_temp += sqrt(lower_temp_series);
				upper_temp += sqrt(upper_temp_series);			
			}
		}
		Pro_sim.push_back(make_pair((*it), (R*L*K*sqrt(T) - lower_temp) / upper_temp));
	}
	sort(Pro_sim.begin(), Pro_sim.end(), sort_LtoS());


	vector<int > range_NN;
	int flag = 0;
	int DTW_count = 0;
	float dtw_dist=0;
	for (vector<pair<int, float> >::iterator it = Pro_sim.begin(); it != Pro_sim.end(); ++it) 
	{
		dtw_dist = DTW_HD(datasets[query_id], datasets[(*it).first]);
		DTW_count++;
		if (dtw_dist <= Epsilon) 
		{
			range_NN.push_back((*it).first);
			flag=0;
		}
		else flag++;
		if (flag == FLAG)
			break;
	}

	for (int l = 0; l<L; l++) {
		for (int k = 0; k<K; k++) {
			delete[]query_hash[l][k];
		}
		delete[]query_hash[l];
	}
	delete[]query_hash;
	cout << "the number of DTW computation is: " << DTW_count << endl;
	return range_NN;

}

vector<int> LSH_Intersection_Pruning_KNN(vector<int> candidate, float**** hash_functions, float**** hash_value, float** query_paa, int query_id, float*** datasets) {
    struct sort_LtoS {
        bool operator()(const std::pair<int, float> &left, const std::pair<int, float> &right) {
            return left.second > right.second;
        }
    };//from large to small
    struct sort_StoL {
        bool operator()(const std::pair<int, float> &left, const std::pair<int, float> &right) {
            return left.second < right.second;
        }
    };//from small to large
    struct sort_int_StoL {
        bool operator()(int left, int right) {
            return left < right;
        }
    };//Int from small to large
    float ***query_hash = CalculateLSH(query_paa, hash_functions);
    
    vector<pair<int, float> > Pro_sim;
    for (vector<int>::iterator it = candidate.begin(); it != candidate.end(); ++it) {
        float lower_temp = 0;
        float upper_temp = 0;
        float lower_temp_series, upper_temp_series;
        for (int l = 0; l<L; l++)
        {
            for (int k = 0; k<K; k++)
            {
                lower_temp_series=0;
                upper_temp_series=0;
                for (int t = 0; t<BlockNum; t++)
                {
                    lower_temp_series += PAAReductionFactor*(query_hash[l][k][t] - hash_value[*it][l][k][t])*(query_hash[l][k][t] - hash_value[*it][l][k][t])*R*R;
                    upper_temp_series += PAAReductionFactor*(abs(query_hash[l][k][t] - hash_value[*it][l][k][t]) + 1)*(abs(query_hash[l][k][t] - hash_value[*it][l][k][t]) + 1)*R*R;
                }
                lower_temp += sqrt(lower_temp_series);
                upper_temp += sqrt(upper_temp_series);
            }
        }
        Pro_sim.push_back(make_pair((*it), (R*L*K*sqrt(T) - lower_temp) / upper_temp));
    }
    sort(Pro_sim.begin(), Pro_sim.end(), sort_LtoS());
    
    
    vector<pair<int,float> > candidate_KNN;
    int DTW_count = 0;
    int count=0;
    for(vector<pair<int, float> >::iterator it=Pro_sim.begin();it!=Pro_sim.end();++it){
        if(count<KNN){
            candidate_KNN.push_back(make_pair((*it).first,DTW_HD(datasets[query_id],datasets[(*it).first])));
            DTW_count++;
            sort(candidate_KNN.begin(),candidate_KNN.end(),sort_LtoS());
        }
        else{
            sort(candidate_KNN.begin(),candidate_KNN.end(),sort_LtoS());
            float temp=DTW_HD(datasets[query_id],datasets[(*it).first]);
            DTW_count++;
            if(temp<candidate_KNN.back().second){
                candidate_KNN.pop_back();
                candidate_KNN.push_back(make_pair((*it).first,temp));
            }
        }
        count++;
    }
    vector<int> KNN_output;
    for(vector<pair<int,float> >::iterator it=candidate_KNN.begin();it!=candidate_KNN.end();++it){
        KNN_output.push_back((*it).first);
        //cout<<(*it).second<<endl;
    }
    sort(KNN_output.begin(), KNN_output.end(), sort_int_StoL());
    
    for (int l = 0; l<L; l++) {
        for (int k = 0; k<K; k++) {
            delete[]query_hash[l][k];
        }
        delete[]query_hash[l];
    }
    delete[]query_hash;
    cout << "the number of DTW computation is: " << DTW_count << endl;
    return KNN_output;
    
}


vector<int> LSH_Intersection_Pruning_entropy(vector<int> candidate, float**** hash_functions, float**** hash_value, float** query_paa, int query_id, float*** datasets) {
	struct sort_LtoS {
		bool operator()(const std::pair<int, float> &left, const std::pair<int, float> &right) {
			return left.second > right.second;
		}
	};//from large to small
	struct sort_StoL {
		bool operator()(const std::pair<int, float> &left, const std::pair<int, float> &right) {
			return left.second < right.second;
		}
	};//from small to large

	float ***query_hash = CalculateLSH(query_paa, hash_functions);

	vector<pair<int, float> > Pro_sim;
	for (vector<int>::iterator it = candidate.begin(); it != candidate.end(); ++it) {
		
		float entropy=0;
		float p;
		float lower_temp_series, upper_temp_series;
		for (int l = 0; l<L; l++) 
		{			
			for (int k = 0; k<K; k++) 
			{	float lower_temp = 0;
		        	float upper_temp = 0;	
				for (int t = 0; t<BlockNum; t++)
				{
					lower_temp += PAAReductionFactor*(query_hash[l][k][t] - hash_value[*it][l][k][t])*(query_hash[l][k][t] - hash_value[*it][l][k][t])*R*R;
					upper_temp += PAAReductionFactor*(abs(query_hash[l][k][t] - hash_value[*it][l][k][t]) + 1)*(abs(query_hash[l][k][t] - hash_value[*it][l][k][t]) + 1)*R*R;
				}
				p=abs(R*sqrt(T) - sqrt(lower_temp)) / sqrt(upper_temp);
				entropy+=-p*log10(p)/log10(2);			
			}
			
		}
		//Pro_sim.push_back(make_pair((*it), (R*sqrt(T*L*K) - sqrt(lower_temp)) / sqrt(upper_temp)));
		Pro_sim.push_back(make_pair((*it), entropy));
	}
	sort(Pro_sim.begin(), Pro_sim.end(), sort_LtoS());



	vector<int > range_NN;
	int flag = 0;
	int DTW_count = 0;
	float dtw_dist=0;
	for (vector<pair<int, float> >::iterator it = Pro_sim.begin(); it != Pro_sim.end(); ++it) 
	{
		dtw_dist = DTW_HD(datasets[query_id], datasets[(*it).first]);
		DTW_count++;
		if (dtw_dist <= Epsilon) 
		{
			range_NN.push_back((*it).first);
			flag=0;
		}
		else flag++;
		if (flag == FLAG)
			break;
	}
	

	for (int l = 0; l<L; l++) {
		for (int k = 0; k<K; k++) {
			delete[]query_hash[l][k];
		}
		delete[]query_hash[l];
	}
	delete[]query_hash;
	cout << "the number of DTW computation is: " << DTW_count << endl;
	return range_NN;

}





vector<int>  LSH_LB_Pruning_range_app(vector<int> candidate, float**** hash_functions, float**** hash_value, float** query_paa, int query_id, float*** datasets) {
	struct sort_pred {
		bool operator()(const std::pair<int, float> &left, const std::pair<int, float> &right) {
			return left.second < right.second;
		}
	};//from small to large
	float ***query_hash = CalculateLSH(query_paa, hash_functions);
	vector<pair<int, float> > lower_bound;
	for (vector<int>::iterator it = candidate.begin(); it != candidate.end(); ++it) {
		float temp=0;
		float temp_series;
		float deviation;
		for (int l = 0; l<L; l++)
		{
			for (int k = 0; k<K; k++) 
			{
				temp_series=0;
				for (int t = 0; t<BlockNum; t++) 
				{
					temp_series+= PAAReductionFactor*(query_hash[l][k][t] - hash_value[*it][l][k][t])*(query_hash[l][k][t] - hash_value[*it][l][k][t])*R*R;
				}
				deviation=-SD+ 2*SD*rand()/double(RAND_MAX);
				temp+=sqrt(temp_series)*(ratio+deviation);
			}			
		}
		lower_bound.push_back(make_pair((*it), temp));
	}
	sort(lower_bound.begin(), lower_bound.end(), sort_pred());




	vector<int > range_NN;
	int flag = 0;
	int DTW_count = 0;
	float dtw_dist=0;
	for (vector<pair<int, float> >::iterator it = lower_bound.begin(); it != lower_bound.end(); ++it) 
	{
		dtw_dist = DTW_HD(datasets[query_id], datasets[(*it).first]);
		DTW_count++;
		if (dtw_dist <= Epsilon) 
		{
			range_NN.push_back((*it).first);
			flag=0;
		}
		else flag++;
		if (flag == FLAG)
			break;
	}
		
			
	for (int l = 0; l<L; l++) {
		for (int k = 0; k<K; k++) {
			delete[]query_hash[l][k];
		}
		delete[]query_hash[l];
	}
	delete[]query_hash;

	cout << "the number of DTW computation is" << DTW_count << endl;

	return range_NN;

}



vector<int>  LSH_UB_Pruning_range_app(vector<int> candidate, float**** hash_functions, float**** hash_value, float** query_paa, int query_id, float*** datasets) {
	struct sort_pred {
		bool operator()(const std::pair<int, float> &left, const std::pair<int, float> &right) {
			return left.second < right.second;
		}
	};//from small to large
	float ***query_hash = CalculateLSH(query_paa, hash_functions);
	vector<pair<int, float> > lower_bound;
	for (vector<int>::iterator it = candidate.begin(); it != candidate.end(); ++it) {
		float temp=0;
		float temp_series;
		float deviation;
		for (int l = 0; l<L; l++)
		{
			for (int k = 0; k<K; k++) 
			{
				temp_series=0;
				for (int t = 0; t<BlockNum; t++) 
				{
					temp_series+= PAAReductionFactor*(abs(query_hash[l][k][t] - hash_value[*it][l][k][t]) + 1)*(abs(query_hash[l][k][t] - hash_value[*it][l][k][t]) + 1)*R*R;
				}
				deviation=-SD+ 2*SD*rand()/double(RAND_MAX);
				temp+=sqrt(temp_series)*(ratio+deviation);
			}			
		}
		lower_bound.push_back(make_pair((*it), temp));
	}
	sort(lower_bound.begin(), lower_bound.end(), sort_pred());




	vector<int > range_NN;
	int flag = 0;
	int DTW_count = 0;
	float dtw_dist=0;
	for (vector<pair<int, float> >::iterator it = lower_bound.begin(); it != lower_bound.end(); ++it) 
	{
		if((*it).second<=Epsilon){
		dtw_dist = DTW_HD(datasets[query_id], datasets[(*it).first]);
		DTW_count++;
		if (dtw_dist <= Epsilon) 
		{
			range_NN.push_back((*it).first);
			flag=0;
		}
		else flag++;}
		
	}
		
			
	for (int l = 0; l<L; l++) {
		for (int k = 0; k<K; k++) {
			delete[]query_hash[l][k];
		}
		delete[]query_hash[l];
	}
	delete[]query_hash;

	cout << "the number of DTW computation is" << DTW_count << endl;

	return range_NN;

}


vector<int> LSH_Intersection_Pruning_KNN_app(vector<int> candidate, float**** hash_functions, float**** hash_value, float** query_paa, int query_id, float*** datasets) {
	struct sort_LtoS {
		bool operator()(const std::pair<int, float> &left, const std::pair<int, float> &right) {
			return left.second > right.second;
		}
	};//from large to small
	struct sort_StoL {
		bool operator()(const std::pair<int, float> &left, const std::pair<int, float> &right) {
			return left.second < right.second;
		}
	};//from small to large
	float ***query_hash = CalculateLSH(query_paa, hash_functions);

	vector<pair<int, float> > Pro_sim;
	for (vector<int>::iterator it = candidate.begin(); it != candidate.end(); ++it) {
		float lower_temp = 0;
		float upper_temp = 0;
		float lower_temp_series, upper_temp_series;
		float deviation;
		for (int l = 0; l<L; l++) 
		{
			for (int k = 0; k<K; k++) 
			{		
				lower_temp_series=0;
				upper_temp_series=0;
				for (int t = 0; t<BlockNum; t++)
				{
					lower_temp_series += PAAReductionFactor*(query_hash[l][k][t] - hash_value[*it][l][k][t])*(query_hash[l][k][t] - hash_value[*it][l][k][t])*R*R;
					upper_temp_series += PAAReductionFactor*(abs(query_hash[l][k][t] - hash_value[*it][l][k][t]) + 1)*(abs(query_hash[l][k][t] - hash_value[*it][l][k][t]) + 1)*R*R;
				}
				deviation=-SD+ 2*SD*rand()/double(RAND_MAX);	
				lower_temp += sqrt(lower_temp_series)*(ratio+deviation);
				upper_temp += sqrt(upper_temp_series)*(ratio+deviation);			
			}
		}
		Pro_sim.push_back(make_pair((*it), (R*L*K*sqrt(T) - lower_temp) / upper_temp));
	}
	sort(Pro_sim.begin(), Pro_sim.end(), sort_LtoS());


	vector<int > range_NN;
	int flag = 0;
	int DTW_count = 0;
	float dtw_dist=0;
	for (vector<pair<int, float> >::iterator it = Pro_sim.begin(); it != Pro_sim.end(); ++it) 
	{
		dtw_dist = DTW_HD(datasets[query_id], datasets[(*it).first]);
		DTW_count++;
		if (dtw_dist <= Epsilon) 
		{
			range_NN.push_back((*it).first);
			flag=0;
		}
		else flag++;
		if (flag == FLAG)
			break;
	}

	for (int l = 0; l<L; l++) {
		for (int k = 0; k<K; k++) {
			delete[]query_hash[l][k];
		}
		delete[]query_hash[l];
	}
	delete[]query_hash;
	cout << "the number of DTW computation is: " << DTW_count << endl;
	return range_NN;

}

pair<vector<int>, int> make_cluster(int left_rep, int right_rep, vector<int> index_left, vector<int> index_right, float*** datasets){
    float** cluster_mean=new float*[T];
    for(int i=0;i<T;i++){
        cluster_mean[i]=new float[D];
    }
    for(int t=0;t<T;t++){
        for(int d=0;d<D;d++){
            for(int i=0;i<index_left.size();i++){
                cluster_mean[t][d]+=datasets[index_left[i]][t][d];
            }
            for(int i=0;i<index_right.size();i++){
                cluster_mean[t][d]+=datasets[index_right[i]][t][d];
            }
            cluster_mean[t][d]=cluster_mean[t][d]/(index_left.size()+index_right.size());
        }
    }
    float variance_smallest=INFINITY;
    int index_rep=left_rep;
    for(int i=0;i<index_left.size();i++){
        float variance_temp=0;
        for(int t=0;t<T;t++){
            for(int d=0;d<D;d++){
                variance_temp+=(datasets[index_left[i]][t][d]-cluster_mean[t][d])*(datasets[index_left[i]][t][d]-cluster_mean[t][d]);
            }
        }
        if(variance_temp<variance_smallest){
            index_rep=index_left[i];
            variance_smallest=variance_temp;
        }
    }
    for(int i=0;i<index_right.size();i++){
        float variance_temp=0;
        for(int t=0;t<T;t++){
            for(int d=0;d<D;d++){
                variance_temp+=(datasets[index_right[i]][t][d]-cluster_mean[t][d])*(datasets[index_right[i]][t][d]-cluster_mean[t][d]);
            }
        }
        if(variance_temp<variance_smallest){
            index_rep=index_right[i];
            variance_smallest=variance_temp;
        }
    }

    vector<int> v;
    v.insert( v.end(), index_left.begin(), index_left.end() );
    v.insert( v.end(), index_right.begin(), index_right.end() );
    
    cout<<"New Cluster: ";
    for(int i=0;i<v.size();i++){
        cout<<v[i]<<" ";
    }
    cout<<"Rep: "<<index_rep<<endl;
    return make_pair(v,index_rep); //use the least variance one as new cluster representation;
    //return make_pair(v,left); //use the first series as new cluster;
}


vector<pair<vector<int>, int > > DTW_hierachical_clustering(int cluster_num, float*** datasets){
    struct sort_StoL {
        bool operator()(const std::pair<pair<int,int>, float> &left, const std::pair<pair<int,int>, float> &right) {
            return left.second < right.second;
        }
    };//from small to large
    
    int DTW_calc_count=0;
    //cluster initialization
    vector<pair<vector<int>, int > > DTW_cluster;//The vector<int> is the index of time series in the cluster, the float** is the centring time series of these indices
    for(int i=0;i<M;i++){
        DTW_cluster.push_back(make_pair(vector<int> (1,i), i));
    }
    for(int i=0;i<M-cluster_num;i++){
        float smallest=INFINITY;
        vector<pair<vector<int>, int > >::iterator iter_index_left;
        vector<pair<vector<int>, int > >::iterator iter_index_right;
        for(vector<pair<vector<int>, int > >::iterator it1=DTW_cluster.begin();it1!=DTW_cluster.end();++it1){
            for(vector<pair<vector<int>, int > >::iterator it2=it1+1;it2!=DTW_cluster.end();++it2){
                float temp=DTW_HD(datasets[(*it1).second],datasets[(*it2).second]);
                DTW_calc_count++;
                if(temp<=smallest){
                    iter_index_left=it1;
                    iter_index_right=it2;
                    smallest=temp;
                }
            }
        }
        //cout<<"left: "<<(*iter_index_left).first[0]<<"; right: "<<(*iter_index_right).first[0]<<endl;
        //cout<<"Distance :"<<smallest<<endl;
        DTW_cluster.push_back(make_cluster((*iter_index_left).second,(*iter_index_right).second,(*iter_index_left).first,(*iter_index_right).first,datasets));
        DTW_cluster.erase(iter_index_right);
        DTW_cluster.erase(iter_index_left);
    }
    
    for(int m=0;m<DTW_cluster.size();m++){
        cout<<"Cluster "<<m+1<<": ";
        for(int i=0;i<DTW_cluster[m].first.size();i++){
            cout<<(DTW_cluster[m].first)[i]<<":"<<datasets[(DTW_cluster[m].first)[i]][0][D]<<", ";
        }
        cout<<endl;
    }
    cout<<"Total number of DTW Calculations: "<<DTW_calc_count<<endl;
    return DTW_cluster;
}

//师姐这个function是按照那篇paper的方法写出的纯LSH Hierachical Clustering，以碰撞最多次为最近邻标准，没有与DTW结合
/*vector<pair<vector<int>, int > > LSH_hierachical_clustering(int cluster_num, float*** datasets, float*** datasets_PAA, float**** hash_functions, float**** hash_value_paa){
    struct sort_StoL {
        bool operator()(const std::pair<pair<int,int>, float> &left, const std::pair<pair<int,int>, float> &right) {
            return left.second < right.second;
        }
    };//from small to large
    
    //cluster initialization
    vector<pair<vector<int>, int > > LSH_cluster;//The vector<int> is the index of time series in the cluster, the float** is the centring time series of these indices
    for(int i=0;i<M;i++){
        LSH_cluster.push_back(make_pair(vector<int> {i}, i));
    }
    
    
    for(int i=0;i<M-cluster_num;i++){
        int count_most=-INFINITY;
        vector<pair<vector<int>, int > >::iterator iter_index_left;
        vector<pair<vector<int>, int > >::iterator iter_index_right;
        for(vector<pair<vector<int>, int > >::iterator it1=LSH_cluster.begin();it1!=LSH_cluster.end();++it1){
            
            float ***query_hash = CalculateLSH(datasets_PAA[(*it1).second], hash_functions);//query_hash[L][K][BlockNum], hashed values for the query series
            for(vector<pair<vector<int>, int > >::iterator it2=it1+1;it2!=LSH_cluster.end();++it2){
                int collision_count=0;
                for (int l = 0; l<L; l++)
                {
                    for (int k = 0; k<K; k++)
                    {
                        for (int n = 0; n<BlockNum; n++)
                        {
                            if (hash_value_paa[(*it2).second][l][k][n] == query_hash[l][k][n])
                            {
                                collision_count++;
                            }
                        }
                    }
                }
                if(collision_count>=count_most){
                    iter_index_left=it1;
                    iter_index_right=it2;
                    count_most=collision_count;
                }
            }
                 
            for (int l = 0; l<L; l++) {
                for (int k = 0; k<K; k++) {
                    delete[]query_hash[l][k];
                }
                delete[]query_hash[l];
            }
            delete[]query_hash;
        }
        //cout<<"Distance :"<<smallest<<endl;
        LSH_cluster.push_back(make_cluster((*iter_index_left).second,(*iter_index_right).second,(*iter_index_left).first,(*iter_index_right).first,datasets));
        LSH_cluster.erase(iter_index_right);
        LSH_cluster.erase(iter_index_left);
    }
    
    for(int m=0;m<LSH_cluster.size();m++){
        cout<<"Cluster "<<m+1<<": ";
        for(int i=0;i<LSH_cluster[m].first.size();i++){
            cout<<(LSH_cluster[m].first)[i]<<":"<<datasets[(LSH_cluster[m].first)[i]][0][D]<<", ";
        }
        cout<<endl;
    }
    
    return LSH_cluster;
}*/

vector<pair<vector<int>, int > > LSH_hierachical_clustering(int cluster_num, float*** datasets, float*** datasets_PAA, float**** hash_functions, float**** hash_value_paa){
    struct sort_StoL {
        bool operator()(const std::pair<pair<int,int>, float> &left, const std::pair<pair<int,int>, float> &right) {
            return left.second < right.second;
        }
    };//from small to large
    
    //cluster initialization
    vector<pair<vector<int>, int > > LSH_cluster;//The vector<int> is the index of time series in the cluster, the float** is the centring time series of these indices
    for(int i=0;i<M;i++){
        LSH_cluster.push_back(make_pair(vector<int> (1,i), i));
    }
    
    int DTW_calc_count=0;
    for(int i=0;i<M-cluster_num;i++){
        float smallest=INFINITY;
        vector<pair<vector<int>, int > >::iterator iter_index_left;
        vector<pair<vector<int>, int > >::iterator iter_index_right;
        for(vector<pair<vector<int>, int > >::iterator it1=LSH_cluster.begin();it1!=LSH_cluster.end();++it1){
            
            float ***query_hash = CalculateLSH(datasets_PAA[(*it1).second], hash_functions);//query_hash[L][K][BlockNum], hashed values for the query series
            for(vector<pair<vector<int>, int > >::iterator it2=it1+1;it2!=LSH_cluster.end();++it2){
                int collision_count=0;
                for (int l = 0; l<L; l++)
                {
                    bool collision=true;
                    for (int k = 0; k<K; k++)
                    {
                        for (int n = 0; n<BlockNum; n++)
                        {
                            if (hash_value_paa[(*it2).second][l][k][n] == query_hash[l][k][n])
                            {
                                collision_count++;
                            }
                            if (collision_count >= threshold) {
                                break;
                            }
                        }
                        if (collision_count<threshold) {
                            collision = false;
                            break;
                        }
                    }
                    if(collision){
                        float temp=DTW_HD(datasets[(*it1).second],datasets[(*it2).second]);
                        DTW_calc_count++;
                        if(temp<=smallest){
                            iter_index_left=it1;
                            iter_index_right=it2;
                            smallest=temp;
                        }
                        break;
                    }
                }
            }
            
            for (int l = 0; l<L; l++) {
                for (int k = 0; k<K; k++) {
                    delete[]query_hash[l][k];
                }
                delete[]query_hash[l];
            }
            delete[]query_hash;
        }
        //cout<<"Distance :"<<smallest<<endl;
        //cout<<"????1: "<<(*iter_index_left).second<<"; "<<"????2: "<<(*iter_index_right).second<<endl;
        LSH_cluster.push_back(make_cluster((*iter_index_left).second,(*iter_index_right).second,(*iter_index_left).first,(*iter_index_right).first,datasets));
        LSH_cluster.erase(iter_index_right);
        LSH_cluster.erase(iter_index_left);
    }
    
    for(int m=0;m<LSH_cluster.size();m++){
        cout<<"Cluster "<<m+1<<": ";
        for(int i=0;i<LSH_cluster[m].first.size();i++){
            cout<<(LSH_cluster[m].first)[i]<<":"<<datasets[(LSH_cluster[m].first)[i]][0][D]<<", ";
        }
        cout<<endl;
    }
    cout<<"Total number of DTW Calculations: "<<DTW_calc_count<<endl;
    return LSH_cluster;
}



float accuracy(vector<int> truth, vector<int> results)
{
	float accuracy;
	float count,acc_count;
	acc_count = 0;
	vector<int>::iterator it;
	vector<int>::iterator it2;

	for (it = truth.begin(); it != truth.end(); ++it)
	{   
		count = 0;
		for (it2 = results.begin(); it2 != results.end(); ++it2)
		{
			if ((*it) == (*it2))
			{
				count += 1;
			}
				
		}
		if (count != 0)
			acc_count += 1;
	}
	//cout << acc_count << endl;
	int size=truth.size();
	//cout << truth.size() << endl;
	accuracy = acc_count / size;
	return accuracy;
}

float accuracy_KNN(vector<int> truth, vector<int> results, int query_id, float*** datasets)
{
    float sum_truth,sum_results=0;
    
    for(int i=0;i<KNN;i++){
        sum_truth+=DTW_HD(datasets[truth[i]],datasets[query_id]);
        sum_results+=DTW_HD(datasets[results[i]],datasets[query_id]);
    }
    float accuracy=sum_results/sum_truth;
    return accuracy;
}

float accuracy_KNN_classification(vector<int> truth, vector<int> results, int query_id, float*** datasets)
{
    int count_truth=0;
    int count_results=0;
    cout<<"Query class type number: "<<datasets[query_id][0][D]<<endl;
    for(int i=0;i<KNN;i++){
        if(datasets[query_id][0][D]==datasets[truth[i]][0][D]){
            count_truth++;
        }
        else {
            cout<<"Groud Truth Wrong Index: "<<results[i]<<", Label: "<<datasets[results[i]][0][D]<<endl;
        }
        if(datasets[query_id][0][D]==datasets[results[i]][0][D]){
            count_results++;
        }
        else {
            cout<<"Result Wrong index: "<<results[i]<<", Label: "<<datasets[results[i]][0][D]<<endl;
        }
    }
    cout<<"Ground Truth KNN classification number: "<<count_truth<<endl;
    cout<<"LSH KNN classification number: "<<count_results<<endl;
    
    float accuracy=float(count_results)/float(count_truth);
    return accuracy;
}

void accuracy_DTW_hierachical_clustering(vector<pair<vector<int>, int > > clusters, float*** datasets){
    float accuracy=0;
    for(int m=0;m<clusters.size();m++){
        cout<<"Cluster "<<m+1<<": ";
        float count_zero=0;
        float count_one=0;
        for(int i=0;i<clusters[m].first.size();i++){
            if(datasets[(clusters[m].first)[i]][0][D]==0){
                count_zero++;
            }
            if(datasets[(clusters[m].first)[i]][0][D]==1){
                count_one++;
            }
            //cout<<(DTW_cluster[m].first)[i]<<":"<<datasets[(DTW_cluster[m].first)[i]][0][D]<<", ";
        }
        if(count_zero>count_one){
            accuracy=count_zero/(count_one+count_zero);
            cout<<"is the zero type with "<<accuracy<<" accuracy"<<endl;
            cout<<"Totally "<<count_zero<<" among "<<count_one+count_zero<<endl;
        }
        else{
            accuracy=count_one/(count_one+count_zero);
            cout<<"is the one type with "<<accuracy<<" accuracy"<<endl;
            cout<<"Totally "<<count_one<<" among "<<count_one+count_zero<<endl;

        }
    }
}

void accuracy_LSH_hierachical_clustering(vector<pair<vector<int>, int > > clusters, float*** datasets){
    float accuracy=0;
    for(int m=0;m<clusters.size();m++){
        cout<<"Cluster "<<m+1<<": ";
        float count_zero=0;
        float count_one=0;
        for(int i=0;i<clusters[m].first.size();i++){
            if(datasets[(clusters[m].first)[i]][0][D]==0){
                count_zero++;
            }
            if(datasets[(clusters[m].first)[i]][0][D]==1){
                count_one++;
            }
        }
        if(count_zero>count_one){
            accuracy=count_zero/(count_one+count_zero);
            cout<<"is the zero type with "<<accuracy<<" accuracy"<<endl;
            cout<<"Totally "<<count_zero<<" among "<<count_one+count_zero<<endl;
        }
        else{
            accuracy=count_one/(count_one+count_zero);
            cout<<"is the one type with "<<accuracy<<" accuracy"<<endl;
            cout<<"Totally "<<count_one<<" among "<<count_one+count_zero<<endl;
            
        }
    }
}
float* generateRandom_vector_r(){
    //Generate r vector
    default_random_engine generator(time(NULL));
    normal_distribution<float> distribution(0.0, 1.0);
    float* random=new float[Size_W];
    for(int i=0;i<Size_W;i++){
        float temp = distribution(generator);
        while (temp<0 || temp>1)
            temp = distribution(generator);
        random[i]=temp;
    }
    return random;
}

vector<int> bit_profile_extraction_onevalue(float* vector_r, float** q){
    vector<int> bit_profile(NB);
    for(int b=0;b<NB;b++){
        float sum=0;
        for(int d=0;d<D;d++){
            for(int w=0;w<Size_W;w++){
                sum+=q[b*Delta+w][d]*vector_r[w];
            }
        }
        if(sum>=0){
            bit_profile[b]=1;
        }
        else{
            bit_profile[b]=-1;
        }
    }
    /*cout<<"Bit Profile 1D: "<<endl;
    for(vector<int>::iterator it = bit_profile.begin(); it != bit_profile.end(); ++it){
        cout<<(*it)<<" ";
    }
    cout<<endl;*/
    return bit_profile;
}

vector< vector<int> > bit_profile_extraction_dvalue(float* vector_r, float** q){
    vector<vector<int > > bit_profile(NB,vector<int >(D));
    for(int b=0;b<NB;b++){
        for(int d=0;d<D;d++){
            float sum=0;
            for(int w=0;w<Size_W;w++){
                sum+=q[b*Delta+w][d]*vector_r[w];
            }
            if(sum>=0){
                bit_profile[b][d]=1;
            }
            else{
                bit_profile[b][d]=-1;
            }
        }
    }
    /*cout<<"Bit Profile HD: "<<endl;
    for(vector< vector<int> >::iterator it = bit_profile.begin(); it != bit_profile.end(); ++it){
        for(vector<int>::iterator it2 = (*it).begin(); it2 != (*it).end(); ++it2){
            cout<<(*it2)<<" ";
        }
        cout<<endl;
    }*/
    return bit_profile;
}

vector<int> generate_n_grams_1d(vector<int> bit_vector){
    vector<int> n_grams(Length_N,0);
    for(int n=0;n<NB-N_grams;n++){
        int index=0;
        int count=N_grams-1;
        for(int i=0;i<N_grams;i++){
            if(bit_vector[n+i]==1){
                index+=pow(2,count);
            }
            count--;
        }
        //cout<<"index: "<<index<<endl;
        n_grams[index]++;
    }
    return n_grams;
}

vector<int> generate_n_grams_hd(vector< vector<int> > bit_vector){
    vector<int> n_grams(Length_N,0);
    for(int n=0;n<NB-N_grams;n++){
        for(int d=0;d<D;d++){
            int index=0;
            int count=N_grams-1;
            for(int i=0;i<N_grams;i++){
                if(bit_vector[n+i][d]==1){
                    index+=pow(2,count);
                }
                count--;
            }
            //cout<<"index: "<<index<<endl;
            n_grams[index]++;
        }
    }
    return n_grams;
}

vector<int> gen_minhash_tables(vector<int> n_grams){
    vector<int> hash_table(HashtableNum);
    int seed=5;
    for(int h=0;h<HashtableNum;h++){
        int hash_value=1;
        //cout<<"seed: "<<seed<<endl;
        srand(seed);
        while(1){
            float random = ((float)rand() / RAND_MAX)* (Length_N - 0);
            float integer;
            float decimal=modf(random,&integer);
            if(decimal<n_grams[integer]/float(NB-N_grams)){
                //cout<<random<<": "<<decimal<<endl;
                //cout<<n_grams[integer]<<"/"<<float(NB-N_grams)<<"="<<n_grams[integer]/float(NB-N_grams)<<endl;
                break;
            }
            hash_value++;
        }
        hash_table[h]=hash_value;
        seed*=3;
    }
    cout<<"Hash Table: "<<endl;
    for(vector<int>::iterator it = hash_table.begin(); it != hash_table.end(); ++it){
        cout<<(*it)<<" ";
    }
    cout<<endl;
    return hash_table;
}

vector<int> SSH_indexing_1d(float** query, float***datasets){
    vector<int> candidate;
    vector<vector<int > > full_hash_tables(M,vector<int >(HashtableNum));
    float* vectorR=generateRandom_vector_r();
    
    vector<int > query_hash_table=gen_minhash_tables(generate_n_grams_1d(bit_profile_extraction_onevalue(vectorR,query)));
    
    for(int m=0;m<M;m++){
        full_hash_tables[m]=gen_minhash_tables(generate_n_grams_1d(bit_profile_extraction_onevalue(vectorR,datasets[m])));
        for(int h=0;h<HashtableNum;h++){
            if(query_hash_table[h]==full_hash_tables[m][h]){
                candidate.push_back(m);
                break;
            }
        }
    }
    
    return candidate;
}

vector<int> SSH_indexing_hd(float** query, float***datasets){
    vector<int> candidate;
    vector<vector<int > > full_hash_tables(M,vector<int >(HashtableNum));
    float* vectorR=generateRandom_vector_r();
    
    vector<int > query_hash_table=gen_minhash_tables(generate_n_grams_hd(bit_profile_extraction_dvalue(vectorR,query)));
    
    for(int m=0;m<M;m++){
        full_hash_tables[m]=gen_minhash_tables(generate_n_grams_hd(bit_profile_extraction_dvalue(vectorR,datasets[m])));
        for(int h=0;h<HashtableNum;h++){
            if(query_hash_table[h]==full_hash_tables[m][h]){
                candidate.push_back(m);
                break;
            }
        }
    }
    
    return candidate;
}

/*vector<int>  SSH_KNN(vector<int> candidate, float** query, float*** datasets) {
    int count = 0;
    struct sort_pred {
        bool operator()(const std::pair<int, float> &left, const std::pair<int, float> &right) {
            return left.second < right.second;
        }
    };
    vector<pair<int, float> > candidate_KNN;
    for (vector<int>::iterator it = candidate.begin(); it != candidate.end(); ++it) {
        if (count<KNN) {
            candidate_KNN.push_back(make_pair((*it), DTW_HD(query, datasets[*it])));
            sort(candidate_KNN.begin(), candidate_KNN.end(), sort_pred());
        }
        else {
            sort(candidate_KNN.begin(), candidate_KNN.end(), sort_pred());
            float temp = DTW_HD(query, datasets[*it]);
            if (temp<candidate_KNN.back().second) {
                candidate_KNN.pop_back();
                candidate_KNN.push_back(make_pair((*it), temp));
            }
        }
        count++;
    }
    vector<int> KNN_output;
    for (vector<pair<int, float> >::iterator it = candidate_KNN.begin(); it != candidate_KNN.end(); ++it) {
        KNN_output.push_back((*it).first);
        //cout<<(*it).second<<endl;
    }
    
    return  KNN_output;
    
}*/

int main()
{
    //load data
	float*** datasets = new float**[M];
	int num = 1;
	int i, j;
	clock_t beginRQ, endRQ;
	double time;
	int query_id=40;

	beginRQ = clock();
	for (i = 0; i<M/2; i++) {
		string count = to_string(num);
		count = "./EEG/class_a/" + count + ".txt";
		num++;
		datasets[i] = load_data(count.c_str(), T, D);
	}
	num = 1;
	for (i = M/2; i<M; i++) {
		string count = to_string(num);
		count = "./EEG/class_c/" + count + ".txt";
		num++;
		datasets[i] = load_data(count.c_str(), T, D);
	}
	endRQ = clock();
	time = double(endRQ - beginRQ) / CLOCKS_PER_SEC;
	cout << "The time for load data: " << time<< " seconds." << endl;
    


	//normalization
	normalization_HD(datasets);
    for(i=0;i<T;i++)
    {
        for(j=0;j<D+1;j++)
        {
            //cout<< datasets[400][i][j]<<" ";
        }
        //cout<<endl;
    }
	cout << "finish normalization" << endl;
    
    
    //Bit Profile Stream Testing
    cout<<"Bit Profile Stream Testing: "<<endl;
    float* vectorR=generateRandom_vector_r();
    vector<int> test=bit_profile_extraction_onevalue(vectorR,datasets[40]);
    /*for(vector<int>::iterator it = test.begin(); it != test.end(); ++it){
        cout<<(*it)<<" ";
    }*/
    //vector< vector<int> > test2=bit_profile_extraction_dvalue(vectorR,datasets[40]);
    cout<<"Size: "<<test.size()<<endl;
    vector<int> grams=generate_n_grams_1d(test);
    for(vector<int>::iterator it = grams.begin(); it != grams.end(); ++it){
        cout<<(*it)<<" ";
    }
    cout<<"Size2: "<<grams.size()<<endl;
    vector<int> hash_tables=gen_minhash_tables(grams);
    for(vector<int>::iterator it = hash_tables.begin(); it != hash_tables.end(); ++it){
        cout<<(*it)<<" ";
    }
    cout<<"Size3: "<<hash_tables.size()<<endl;
    cout<<"/****************************************************************************/"<<endl;
    
	//cout << "LB_PAA Test: " << compute_LB_PAA_HD(datasets[0], datasets[2]) << endl;
    clock_t DTW_onceBegin=clock();
	cout << "DTW_HD Test: " << DTW_HD(datasets[query_id], datasets[2]) << endl;
    clock_t DTW_onceEnd=clock();
    double DTW_once = double(DTW_onceEnd - DTW_onceBegin) / CLOCKS_PER_SEC;
    cout << "The time for DTW calculation once: " << DTW_once<< " seconds." << endl;
	//cout << "DTW_1D Test: " << DTW_1D(datasets[0], datasets[2]) << endl;
	cout << "Euclidean distance Test: " << distance_HD(datasets[query_id], datasets[2])<< endl;
    cout<<"/****************************************************************************/"<<endl;
    
    //DTW Hierachical Clustering Ground Truth
    /*cout<<"DTW Hierachical Clustering Ground Truth: "<<endl;
    clock_t beginDTWHC = clock();
    vector<pair<vector<int>, int > > DTW_clusters=DTW_hierachical_clustering(ClusterNum, datasets);
    clock_t endDTWHC = clock();
    double elapsed_secsDTWHC = double(endDTWHC - beginDTWHC) / CLOCKS_PER_SEC;
    cout<<"The time spent for DTW Hierachical Clustering ground truth: "<< elapsed_secsDTWHC<<" seconds."<<endl;
    accuracy_DTW_hierachical_clustering(DTW_clusters, datasets);*/
    cout<<"/****************************************************************************/"<<endl;
	
	//DTW Range Query Ground Truth
	/*cout << "DTW Range Query Ground Truth: " << endl;
        beginRQ = clock();
	int count = 0;
	vector<int> DTW_groundtruth_Range = DTW_GroundTruth_Range(datasets[query_id], datasets);
	for (vector<int >::iterator it = DTW_groundtruth_Range.begin(); it != DTW_groundtruth_Range.end(); ++it) {
		cout << "Candidate series number for DTW range query ground truth: " << (*it)<< endl;
		count++;
	}
	cout << "The total number of series for DTW range query ground truth: " << count << endl;
	endRQ = clock();
	double elapsed_secsRQ = double(endRQ - beginRQ) / CLOCKS_PER_SEC;
	cout << "The time spent for DTW range query ground truth: " << elapsed_secsRQ << " seconds." << endl;*/
	//cout << "/****************************************************************************/" << endl;


    //DTW KNN Query Ground Truth
    /*cout<<"DTW KNN Query Ground Truth: "<<endl;
    clock_t beginDTWKNN = clock();
    int countDTWKNN=0;
    vector<int> DTW_groundtruth_KNN=DTW_GroundTruth_KNN(datasets[query_id],datasets);
    for(vector<int>::iterator it=DTW_groundtruth_KNN.begin();it!=DTW_groundtruth_KNN.end();++it){
        cout<<"Candidate series number for DTW KNN Query ground truth: "<<(*it)<<endl;
        countDTWKNN++;
    }
    cout<<"The total number of candidate series for DTW KNN Query: "<<countDTWKNN<<endl;
    clock_t endDTWKNN = clock();
    double elapsed_secsDTWKNN = double(endDTWKNN - beginDTWKNN) / CLOCKS_PER_SEC;
    cout<<"The time spent for DTW KNN Query ground truth: "<< elapsed_secsDTWKNN<<" seconds."<<endl;*/
    cout<<"/****************************************************************************/"<<endl;
    
    //SSH indexing 1D
    cout<<"SSH Query Indexing: "<<endl;
    clock_t SSH_begin = clock();
    vector<int> SSH_candidate=SSH_indexing_1d(datasets[query_id],datasets);
    cout << "The number of SSH cadidates: " << SSH_candidate.size()<< "." << endl;
    for(vector<int>::iterator it=SSH_candidate.begin();it!=SSH_candidate.end();++it){
        //cout<<"Candidate Index: "<<(*it)<<endl;
    }
    clock_t SSH_end = clock();
    double elapsed_secsSSH = double(SSH_end - SSH_begin) / CLOCKS_PER_SEC;
    cout<<"The time spent for SSH indexing: "<< elapsed_secsSSH<<" seconds."<<endl;
    cout<<"/****************************************************************************/"<<endl;
    
    //SSH indexing HD
    cout<<"SSH Query Indexing: "<<endl;
    clock_t SSH_begin_hd = clock();
    vector<int> SSH_candidate_hd=SSH_indexing_hd(datasets[query_id],datasets);
    cout << "The number of SSH cadidates HD: " << SSH_candidate_hd.size()<< "." << endl;
    for(vector<int>::iterator it=SSH_candidate_hd.begin();it!=SSH_candidate_hd.end();++it){
        //cout<<"Candidate Index: "<<(*it)<<endl;
    }
    clock_t SSH_end_hd = clock();
    double elapsed_secsSSH_hd = double(SSH_end_hd - SSH_begin_hd) / CLOCKS_PER_SEC;
    cout<<"The time spent for SSH indexing HD: "<< elapsed_secsSSH_hd<<" seconds."<<endl;
    cout<<"/****************************************************************************/"<<endl;
    
    //SSH KNN
    /*cout<<"SSH KNN: "<<endl;
    clock_t SSHKNN_begin = clock();
    vector<int> ssh_KNN=SSH_KNN(SSH_candidate,datasets[query_id],datasets);
    cout << "The number of SSH KNN: " << ssh_KNN.size()<< "." << endl;
    for (vector<int>::iterator it = ssh_KNN.begin(); it != ssh_KNN.end(); ++it) {
        cout << "Candidate series number for SSH KNN: " << (*it) << endl;
    }
    clock_t SSHKNN_end = clock();
    double elapsed_secs_SSHKNN = double(SSHKNN_end - SSHKNN_begin) / CLOCKS_PER_SEC;*/
    //cout << "the accuracy of direct SSH KNN: " << accuracy_KNN(DTW_groundtruth_KNN, ssh_KNN, query_id, datasets) << endl;
    //cout << "the accuracy of direct SSH KNN Label classification: " << accuracy_KNN_classification(DTW_groundtruth_KNN, ssh_KNN, query_id, datasets) << endl;
    //cout<<"The time spent for SSH KNN: "<< elapsed_secs_SSHKNN<<" seconds."<<endl;
    cout<<"/****************************************************************************/"<<endl;
    
	//LSH method
	cout << "LSH method: " << endl;
	float ***dataset_PAA = compute_LSH_PAA_datasets(datasets);// calculate PAA representation for the whole datasets
	float ****hash_functions = generateRandom();//hash_functions[L][K][D]
	//float ****hash_value = CalculateLSH(datasets, hash_functions);//hash_value[M][L][K][T], hashed values for the whole datasets
	float ****hash_value = CalculateLSH(dataset_PAA, hash_functions);//hash_value[M][L][K][BlockNum], hashed values for the whole datasets_PAA

       //LSH R Envelope Ground Truth
	clock_t beginREnvelope = clock();
	vector<int> candidate_LSH_REnvelope = REnvelope_GroundTruth(datasets[query_id], datasets);
	int LSH_REnvelope_count = 0;
	for (vector<int>::iterator it = candidate_LSH_REnvelope.begin(); it != candidate_LSH_REnvelope.end(); ++it) {
		//cout << "Candidate series number for LSH R envelope ground truth: " << (*it) << endl;
		LSH_REnvelope_count++;
	}
	cout << "The total number of series for LSH R envelope ground truth: " << LSH_REnvelope_count << endl;
	clock_t endREnvelope = clock();
	double elapsed_secsREnvelope = double(endREnvelope - beginREnvelope) / CLOCKS_PER_SEC;
	cout << "The time spent for LSH R envelope ground truth: " << elapsed_secsREnvelope << " seconds." << endl;
	cout << "****************************************************************************" << endl;


	

	//LSH basic
	/*clock_t beginLSH = clock();
	vector<int> candidateLSH = LSH_query(datasets[query_id], hash_functions, hash_value);
	int LSH_count = 0;
	for (vector<int>::iterator it = candidateLSH.begin(); it != candidateLSH.end(); ++it) {
		//cout << "Candidate series number for LSH querying: " << (*it) << endl;
		LSH_count++;
	}
	cout << "The total number of candidate series for LSH querying: " << LSH_count << endl;
	clock_t endLSH = clock();
	double elapsed_secsLSH = double(endLSH - beginLSH) / CLOCKS_PER_SEC;
	cout << "The time spent for LSH querying: " << elapsed_secsLSH << " seconds." << endl;
	cout << "the accuracy of LSH r-envolop query: " << accuracy(candidate_LSH_REnvelope, candidateLSH) << endl;*/
	cout <<"****************************************************************************" << endl;

    //LSH Hierachical Clustering Ground Truth
    /*cout<<"LSH Hierachical Clustering Ground Truth: "<<endl;
    clock_t beginLSHHC = clock();
    vector<pair<vector<int>, int > > LSH_clusters=LSH_hierachical_clustering(ClusterNum, datasets, dataset_PAA, hash_functions, hash_value);
    clock_t endLSHHC = clock();
    double elapsed_secsLSHHC = double(endLSHHC - beginLSHHC) / CLOCKS_PER_SEC;
    cout<<"The time spent for LSH Hierachical Clustering ground truth: "<< elapsed_secsLSHHC<<" seconds."<<endl;
    accuracy_LSH_hierachical_clustering(LSH_clusters, datasets);*/
    cout<<"/****************************************************************************/"<<endl;
    
    //LSH range NN without pruning
	/*clock_t beginLSH_range_NN = clock();
	vector<int>  candidateLSH_range_NN = LSH_range_NN(candidateLSH, datasets[query_id], datasets);
	int LSH_range_NN_count = 0;
	for (vector<int> ::iterator it = candidateLSH_range_NN.begin(); it != candidateLSH_range_NN.end(); ++it) {
		//cout << "Candidate series number for LSH range NN without pruning: " << (*it) << endl;
		LSH_range_NN_count++;
	}
	cout << "The total number of series that dtw< epsilon in the lsh candidate set (LSH range NN without pruning): " << LSH_range_NN_count << endl;
	clock_t endLSH_range_NN = clock();
	double elapsed_secsLSH_range_NN = double(endLSH_range_NN - beginLSH_range_NN) / CLOCKS_PER_SEC;
	cout << "The time spent for LSH range NN without pruning: " << elapsed_secsLSH_range_NN << " seconds." << endl;
        cout << "the accuracy of LSH range NN query: " << accuracy(DTW_groundtruth_Range, candidateLSH_range_NN) << endl;*/
	//cout << "****************************************************************************" << endl;
	

	//LSH range NN with LB pruning
	/*clock_t beginLSH_range_NN_LB = clock();
	vector<int > candidateLSH_range_NN_LB = LSH_LB_Pruning_range(candidateLSH, hash_functions, hash_value, dataset_PAA[query_id],query_id, datasets);
	int LSH_range_NN_LB_count = 0;
	for (vector<int >::iterator it = candidateLSH_range_NN_LB.begin(); it != candidateLSH_range_NN_LB.end(); ++it) {
		//cout << "Candidate series number for LSH range NN with LB pruning: " << (*it)<<endl;
		LSH_range_NN_LB_count++;
	}
	cout << "The total number of candidate series for LSH range NN with LB pruning: " << LSH_range_NN_LB_count << endl;
	clock_t endLSH_range_NN_LB = clock();
	double elapsed_secsLSH_range_NN_LB = double(endLSH_range_NN_LB - beginLSH_range_NN_LB) / CLOCKS_PER_SEC;
	cout << "The time spent for LSH range NN with LB pruning: " << elapsed_secsLSH_range_NN_LB << " seconds." << endl;
        cout << "the accuracy of LSH-LB pruning range NN query: " << accuracy(DTW_groundtruth_Range, candidateLSH_range_NN_LB) << endl;*/
	//cout << "****************************************************************************" << endl;


        //LSH range NN with Intersection pruning
	/*clock_t beginLSH_range_NN_Intersection = clock();
	vector<int> candidateLSH_range_NN_Intersection = LSH_Intersection_Pruning_range(candidateLSH, hash_functions, hash_value, dataset_PAA[query_id],query_id,  datasets);
	int LSH_range_NN_Intersection_count = 0;
	for (vector<int>::iterator it = candidateLSH_range_NN_Intersection.begin(); it != candidateLSH_range_NN_Intersection.end(); ++it) {
		//cout << "Candidate series number for LSH range NN with Intersection pruning: " << (*it) << endl;
		LSH_range_NN_Intersection_count++;
	}
	cout << "The total number of candidate series for LSH range NN with Intersection pruning: " << LSH_range_NN_Intersection_count << endl;
	clock_t endLSH_range_NN_Intersection = clock();
	double elapsed_secsLSH_range_NN_Intersection = double(endLSH_range_NN_Intersection - beginLSH_range_NN_Intersection) / CLOCKS_PER_SEC;
	cout << "The time spent for LSH range NN with Intersection pruning: " << elapsed_secsLSH_range_NN_Intersection << " seconds." << endl;
        cout << "the accuracy of LSH-Intersection pruning range NN query: " << accuracy(DTW_groundtruth_Range, candidateLSH_range_NN_Intersection) << endl;*/
	//cout << "****************************************************************************" << endl;

        //LSH range NN with Intersection pruning (entropy)
	/*clock_t beginLSH_range_NN_Intersection_entropy = clock();
	vector<int> candidateLSH_range_NN_Intersection_entropy = LSH_Intersection_Pruning_entropy(candidateLSH, hash_functions, hash_value, dataset_PAA[query_id],query_id,  datasets);
	int LSH_range_NN_Intersection_entropy_count = 0;
	for (vector<int>::iterator it = candidateLSH_range_NN_Intersection_entropy.begin(); it != candidateLSH_range_NN_Intersection_entropy.end(); ++it) {
		//cout << "Candidate series number for LSH range NN with Intersection pruning entropy: " << (*it) << endl;
		LSH_range_NN_Intersection_entropy_count++;
	}
	cout << "The total number of candidate series for LSH range NN with Intersection pruning entropy: " << LSH_range_NN_Intersection_entropy_count << endl;
	clock_t endLSH_range_NN_Intersection_entropy = clock();
	double elapsed_secsLSH_range_NN_Intersection_entropy = double(endLSH_range_NN_Intersection_entropy - beginLSH_range_NN_Intersection_entropy) / CLOCKS_PER_SEC;
	cout << "The time spent for LSH range NN with Intersection pruning entropy: " << elapsed_secsLSH_range_NN_Intersection_entropy << " seconds." << endl;
        cout << "the accuracy of LSH-Intersection pruning entropy range NN query: " << accuracy(DTW_groundtruth_Range, candidateLSH_range_NN_Intersection_entropy) << endl;*/
	//cout << "****************************************************************************" << endl;
   
	//LSH range NN with LB pruning (APPROXIMATE DTW bound)
	/*cout<<"use LB pruning (approximate dtw bound):"<<endl;
	clock_t beginLSH_range_NN_LB_app = clock();
	vector<int > candidateLSH_range_NN_LB_app = LSH_LB_Pruning_range_app(candidateLSH, hash_functions, hash_value, dataset_PAA[query_id],query_id, datasets);
	int LSH_range_NN_LB_count_app = 0;
	for (vector<int >::iterator it = candidateLSH_range_NN_LB_app.begin(); it != candidateLSH_range_NN_LB_app.end(); ++it) {
		//cout << "Candidate series number for LSH range NN with LB pruning: " << (*it)<<endl;
		LSH_range_NN_LB_count_app++;
	}
	cout << "The total number of candidate series for LSH range NN with LB pruning (approximate dtw bound): " << LSH_range_NN_LB_count_app << endl;
	clock_t endLSH_range_NN_LB_app = clock();
	double elapsed_secsLSH_range_NN_LB_app = double(endLSH_range_NN_LB_app - beginLSH_range_NN_LB_app) / CLOCKS_PER_SEC;
	cout << "The time spent for LSH range NN with LB pruning(approximate dtw bound) : " << elapsed_secsLSH_range_NN_LB_app << " seconds." << endl;
        cout << "the accuracy of LSH-LB pruning range NN query (approximate dtw bound): " << accuracy(DTW_groundtruth_Range, candidateLSH_range_NN_LB_app) << endl;*/
	//cout << "****************************************************************************" << endl;


        //LSH range NN with Intersection pruning (APPROXIMATE DTW bound)
	/*cout<<"use Intersection pruning (approximate dtw bound):"<<endl;
	clock_t beginLSH_range_NN_Intersection_app = clock();
	vector<int> candidateLSH_range_NN_Intersection_app = LSH_Intersection_Pruning_range_app(candidateLSH, hash_functions, hash_value, dataset_PAA[query_id],query_id,  datasets);
	int LSH_range_NN_Intersection_count_app = 0;
	for (vector<int>::iterator it = candidateLSH_range_NN_Intersection_app.begin(); it != candidateLSH_range_NN_Intersection_app.end(); ++it) {
		//cout << "Candidate series number for LSH range NN with Intersection pruning: " << (*it) << endl;
		LSH_range_NN_Intersection_count_app++;
	}
	cout << "The total number of candidate series for LSH range NN with Intersection pruning(approximate dtw bound): " << LSH_range_NN_Intersection_count_app << endl;
	clock_t endLSH_range_NN_Intersection_app = clock();
	double elapsed_secsLSH_range_NN_Intersection_app = double(endLSH_range_NN_Intersection_app - beginLSH_range_NN_Intersection_app) / CLOCKS_PER_SEC;
	cout << "The time spent for LSH range NN with Intersection pruning(approximate dtw bound): " << elapsed_secsLSH_range_NN_Intersection_app << " seconds." << endl;
        cout << "the accuracy of LSH-Intersection pruning range NN query: " << accuracy(DTW_groundtruth_Range, candidateLSH_range_NN_Intersection_app) << endl;*/
	//cout << "****************************************************************************" << endl;
  
        
        //return range nn based on LB pruning
    /*vector<int> setID;
	for(int i=0;i<M;i++)
	setID.push_back(i);
	cout<<"directly use LB pruning:"<<endl;
	clock_t begin_range_NN_LB = clock();
	vector<int > candidate_range_NN_LB = LSH_LB_Pruning_range(setID, hash_functions, hash_value, dataset_PAA[query_id],query_id, datasets);
	int range_NN_LB_count = 0;
	for (vector<int >::iterator it = candidate_range_NN_LB.begin(); it != candidate_range_NN_LB.end(); ++it) {
		//cout << "Candidate series number for LSH range NN with LB pruning: " << (*it)<<endl;
		range_NN_LB_count++;
	}
	cout << "The total number of candidate series for range NN with LB pruning: " << range_NN_LB_count << endl;
	clock_t end_range_NN_LB = clock();
	double elapsed_secs_range_NN_LB = double(end_range_NN_LB - begin_range_NN_LB) / CLOCKS_PER_SEC;
	cout << "The time spent for LSH range NN with LB pruning: " << elapsed_secs_range_NN_LB << " seconds." << endl;
        //cout << "the accuracy of direct LB pruning range NN query: " << accuracy(DTW_groundtruth_Range, candidate_range_NN_LB) << endl;*/
	cout << "****************************************************************************" << endl;


	//return range NN based on Intersection pruning
        /*cout<<"directly use intersection pruning:"<<endl;
	clock_t begin_range_NN_Intersection = clock();
	vector<int> candidate_range_NN_Intersection = LSH_Intersection_Pruning_range(setID, hash_functions, hash_value, dataset_PAA[query_id],query_id,  datasets);
	int range_NN_Intersection_count = 0;
	for (vector<int>::iterator it = candidate_range_NN_Intersection.begin(); it != candidate_range_NN_Intersection.end(); ++it) {
		//cout << "Candidate series number for range NN with Intersection pruning: " << (*it) << endl;
		range_NN_Intersection_count++;
	}
	cout << "The total number of candidate series for range NN with Intersection pruning: " << range_NN_Intersection_count << endl;
	clock_t end_range_NN_Intersection = clock();
	double elapsed_secs_range_NN_Intersection = double(end_range_NN_Intersection - begin_range_NN_Intersection) / CLOCKS_PER_SEC;
	cout << "The time spent for LSH range NN with Intersection pruning: " << elapsed_secs_range_NN_Intersection << " seconds." << endl;
        cout << "the accuracy of direct Intersection pruning range NN query: " << accuracy(DTW_groundtruth_Range, candidate_range_NN_Intersection) << endl;*/
	//cout << "/****************************************************************************/" << endl;
    
    //return KNN based on Intersection pruning
    /*cout<<"directly use intersection pruning KNN:"<<endl;
    clock_t begin_KNN_Intersection = clock();
    vector<int> candidate_KNN_Intersection = LSH_Intersection_Pruning_KNN(setID, hash_functions, hash_value, dataset_PAA[query_id],query_id,  datasets);
    int KNN_Intersection_count = 0;
    for (vector<int>::iterator it = candidate_KNN_Intersection.begin(); it != candidate_KNN_Intersection.end(); ++it) {
        cout << "Candidate series number for KNN with Intersection pruning: " << (*it) << endl;
        KNN_Intersection_count++;
    }
    cout << "The total number of candidate series for KNN with Intersection pruning: " << KNN_Intersection_count << endl;
    clock_t end_KNN_Intersection = clock();
    double elapsed_secs_KNN_Intersection = double(end_KNN_Intersection - begin_KNN_Intersection) / CLOCKS_PER_SEC;
    cout << "The time spent for LSH KNN with Intersection pruning: " << elapsed_secs_KNN_Intersection << " seconds." << endl;
    cout << "the accuracy of direct Intersection pruning KNN: " << accuracy_KNN(DTW_groundtruth_KNN, candidate_KNN_Intersection, query_id, datasets) << endl;
    cout << "the accuracy of direct Intersection pruning KNN classification: " << accuracy_KNN_classification(DTW_groundtruth_KNN, candidate_KNN_Intersection, query_id, datasets) << endl;*/
    cout << "/****************************************************************************/" << endl;
    
    //return range nn based on LB pruning(APPROXIMATE DTW bound)
	/*cout<<"directly use LB pruning(approximate dtw):"<<endl;
	clock_t begin_range_NN_LB_app = clock();
	vector<int > candidate_range_NN_LB_app = LSH_LB_Pruning_range_app(setID, hash_functions, hash_value, dataset_PAA[query_id],query_id, datasets);
	int range_NN_LB_count_app = 0;
	for (vector<int >::iterator it = candidate_range_NN_LB_app.begin(); it != candidate_range_NN_LB_app.end(); ++it) {
		//cout << "Candidate series number for LSH range NN with LB pruning: " << (*it)<<endl;
		range_NN_LB_count_app++;
	}
	cout << "The total number of candidate series for range NN with LB pruning(approximate dtw): " << range_NN_LB_count_app<< endl;
	clock_t end_range_NN_LB_app = clock();
	double elapsed_secs_range_NN_LB_app = double(end_range_NN_LB_app - begin_range_NN_LB_app) / CLOCKS_PER_SEC;
	cout << "The time spent for LSH range NN with LB pruning(approximate dtw): " << elapsed_secs_range_NN_LB_app << " seconds." << endl;
        cout << "the accuracy of direct LB pruning range NN query(approximate dtw): " << accuracy(DTW_groundtruth_Range, candidate_range_NN_LB_app) << endl;*/
	//cout << "****************************************************************************" << endl;


	//return range NN based on Intersection pruning(APPROXIMATE DTW bound)
        /*cout<<"directly use intersection pruning(approximate dtw):"<<endl;
	clock_t begin_range_NN_Intersection_app = clock();
	vector<int> candidate_range_NN_Intersection_app = LSH_Intersection_Pruning_range_app(setID, hash_functions, hash_value, dataset_PAA[query_id],query_id,  datasets);
	int range_NN_Intersection_count_app = 0;
	for (vector<int>::iterator it = candidate_range_NN_Intersection_app.begin(); it != candidate_range_NN_Intersection_app.end(); ++it) {
		//cout << "Candidate series number for range NN with Intersection pruning: " << (*it) << endl;
		range_NN_Intersection_count_app++;
	}
	cout << "The total number of candidate series for range NN with Intersection pruning(approximate dtw): " << range_NN_Intersection_count_app << endl;
	clock_t end_range_NN_Intersection_app = clock();
	double elapsed_secs_range_NN_Intersection_app = double(end_range_NN_Intersection_app - begin_range_NN_Intersection_app) / CLOCKS_PER_SEC;
	cout << "The time spent for LSH range NN with Intersection pruning(approximate dtw): " << elapsed_secs_range_NN_Intersection_app << " seconds." << endl;
        cout << "the accuracy of direct Intersection pruning range NN query (approximate dtw): " << accuracy(DTW_groundtruth_Range, candidate_range_NN_Intersection_app) << endl;*/
	//cout << "/****************************************************************************/" << endl;
	


        //return range NN based on Intersection pruning (entropy)
	/*cout<<"directly use intersection pruning (entropy):"<<endl;
	clock_t begin_range_NN_Intersection_entropy = clock();
	vector<int> candidate_range_NN_Intersection_entropy = LSH_Intersection_Pruning_entropy(setID,hash_functions, hash_value, dataset_PAA[query_id],query_id,  datasets);
	int range_NN_Intersection_entropy_count = 0;
	for (vector<int>::iterator it = candidate_range_NN_Intersection_entropy.begin(); it != candidate_range_NN_Intersection_entropy.end(); ++it) {
		//cout << "Candidate series number for range NN with Intersection pruning entropy: " << (*it) << endl;
		range_NN_Intersection_entropy_count++;
	}
	cout << "The total number of candidate series for direct range NN with Intersection pruning entropy: " << range_NN_Intersection_entropy_count << endl;
	clock_t end_range_NN_Intersection_entropy = clock();
	double elapsed_secs_range_NN_Intersection_entropy = double(end_range_NN_Intersection_entropy - begin_range_NN_Intersection_entropy) / CLOCKS_PER_SEC;
	cout << "The time spent for direct range NN with Intersection pruning entropy: " << elapsed_secs_range_NN_Intersection_entropy << " seconds." << endl;
        cout << "the accuracy of Intersection pruning entropy range NN query: " << accuracy(DTW_groundtruth_Range, candidate_range_NN_Intersection_entropy) << endl;*/
	//cout << "****************************************************************************" << endl;
   
    
    


	for (int i = 0; i < M; i++) {
		for (int j = 0; j<T; j++) {
			delete[]datasets[i][j];
		}
		delete[] datasets[i];
	}
	delete[] datasets;

        
	for (int m = 0; m < M; m++) {
		for (int l = 0; l<L; l++) {
			for (int k = 0; k<K; k++) {
				delete[]hash_value[m][l][k];
			}
			delete[]hash_value[m][l];
		}
		delete[]hash_value[m];
	}
	delete[] hash_value;

	for (int l = 0; l<L; l++) {
		for (int k = 0; k<K; k++) {
			for(int t=0; t<LSHfunc; t++){
				delete[]hash_functions[l][k][t];
			}
			delete[]hash_functions[l][k];
		}
		delete[]hash_functions[l];
	}
	delete[]hash_functions;


	return 0;
}

	
	








