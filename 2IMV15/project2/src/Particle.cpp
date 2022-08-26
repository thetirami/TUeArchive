#include "Particle.h"
#include <GL/glut.h>

#ifndef PI
#define PI 3.14159265358979323846
#endif

Particle::Particle(const Eigen::Vector2f &constructPos, double m, int ind, PTYPE pType) :
        _initPos(constructPos), _pos(constructPos), _v(Eigen::Vector2f(0.0, 0.0)), _m(m), _ind(ind), _pType(pType){
    if (_pType != NORMAL) {
        reset();
        setBoundBox();
    }
}


Particle::~Particle() = default;

void Particle::reset() {
	_pos = _initPos;
	_v = Eigen::Vector2f(0.0, 0.0);
	_f = Eigen::Vector2f(0.0, 0.0);
    _massCenter = _initPos;
    _inertia = _m * (pow(_dimension/2, 2) + pow(_dimension/2, 2));
    _r = Eigen::Matrix2f::Identity();
    _lm = Eigen::Vector2f(0, 0);
    _am = 0.0f;
    _omega = _am / (_inertia+0.001);
    _torque = 0.0f;
    _angle = 0.0f * PI / 180;
}

void Particle::draw() {
    const float h = 12.f;
    if (_pType == NORMAL) {
        glColor3f(1.f, 1.f, 1.f); //rgb
        glPointSize(h);
        glBegin(GL_POINTS);
        glVertex2f(_pos[0], _pos[1]);
        glEnd();
    } else {
        glColor3f(0.8, 0.7, 0.2);
        glBegin(GL_POLYGON);
        glVertex2f(_corner[0][0], _corner[0][1]);
        glVertex2f(_corner[1][0], _corner[1][1]);
        glVertex2f(_corner[2][0], _corner[2][1]);
        glVertex2f(_corner[3][0], _corner[3][1]);
        glVertex2f(_corner[0][0], _corner[0][1]);
        glEnd();
    }
}

void Particle::setBoundBox() {
    _corner.emplace_back(-_dimension / 2,  _dimension / 2);	// top left
    _corner.emplace_back( _dimension / 2,  _dimension / 2);	// top right
    _corner.emplace_back( _dimension / 2, -_dimension / 2);	// bottom right
    _corner.emplace_back(-_dimension / 2, -_dimension / 2); // bottom left
    for (auto & k : _corner) {
        k = _r * k + _massCenter;
    }
}

std::vector<Eigen::Vector2f> Particle::getClosestEdge(const Eigen::Vector2f& point) {
    int idx = 0;
    int n = _corner.size();
    float minDist = std::numeric_limits<float>::max();
    float currDist;
    for (int i = 0; i < n; i++) {
        currDist = minDistance(_corner[i % n], _corner[(i + 1) % n], point);
        if (minDist >= currDist) {
            idx = i;
            minDist = currDist;
        }
    }
    return std::vector<Eigen::Vector2f>({_corner[idx], _corner[(idx + 1) % n]});
}

std::vector<Eigen::Vector4f> Particle::boundGrid(int nGrid) {
    std::vector<Eigen::Vector4f> bound_grids;
    std::vector<Eigen::Vector2i> corner_absolute;
    Eigen::Vector4f temp4f, result;
    Eigen::Vector2i temp2i;
    Eigen::Vector2i top, bottom, left, right;
    Eigen::Vector2f grid_center, vector_length;
    int l_i, r_i, t_i, b_i;
    float grid_length = 2.0 / nGrid;
    for (int i = 0; i < 4; i++) {
        temp2i[0] = int((_corner[i][0] - (-1)) / grid_length);
        temp2i[1] = int((1 - _corner[i][1]) / grid_length);
        corner_absolute.push_back(temp2i);
    }
    left = corner_absolute[0];
    right = corner_absolute[0];
    top = corner_absolute[0];
    bottom = corner_absolute[0];
    l_i = r_i = t_i = b_i = 0;
    for (int i = 1; i < 4; i++) {
        if (corner_absolute[i][0] > right[0]) {
            right = corner_absolute[i];
            r_i = i;
        }
        if (corner_absolute[i][0] < left[0]) {
            left = corner_absolute[i];
            l_i = i;
        }
        if (corner_absolute[i][1] < top[1]) {
            top = corner_absolute[i];
            t_i = i;
        }
        if (corner_absolute[i][1] > bottom[1]) {
            bottom = corner_absolute[i];
            b_i = i;
        }
    }
    // parallel
    if (corner_absolute[0][1] == corner_absolute[1][1] || corner_absolute[0][0] == corner_absolute[1][0]) {
        for (int i = left[0]; i < right[0]; i++) {
            grid_center[0] = i * grid_length + (grid_length / 2) - 1;
            grid_center[1] = (1 - top[1] * grid_length) - (grid_length / 2);
            vector_length = grid_center - _pos;
            temp4f[0] = float(i + 1);				  //i
            temp4f[1] = float(nGrid - (top[1] + 1)); //j
            temp4f[2] = vector_length[0];
            temp4f[3] = vector_length[1];
            bound_grids.push_back(temp4f);
        }
        for (int j = top[1]; j < bottom[1]; j++) {
            grid_center[0] = right[0] * grid_length + (grid_length / 2) - 1;
            grid_center[1] = (1 - j * grid_length) - (grid_length / 2);
            vector_length = grid_center - _pos;
            temp4f[0] = float(right[0] + 1);	 //i
            temp4f[1] = float(nGrid - (j + 1)); //j
            temp4f[2] = vector_length[0];
            temp4f[3] = vector_length[1];
            bound_grids.push_back(temp4f);
        }
        for (int i = right[0]; i > left[0]; i--) {
            grid_center[0] = i * grid_length + (grid_length / 2) - 1;
            grid_center[1] = (1 - bottom[1] * grid_length) - (grid_length / 2);
            vector_length = grid_center - _pos;
            temp4f[0] = float(i + 1);					 //i
            temp4f[1] = float(nGrid - (bottom[1] + 1)); //j
            temp4f[2] = vector_length[0];
            temp4f[3] = vector_length[1];
            bound_grids.push_back(temp4f);
        }
        for (int j = bottom[1]; j > top[1]; j--) {
            grid_center[0] = left[0] * grid_length + (grid_length / 2) - 1;
            grid_center[1] = (1 - j * grid_length) - (grid_length / 2);
            vector_length = grid_center - _pos;
            temp4f[0] = float(left[0] + 1);		 //i
            temp4f[1] = float(nGrid - (j + 1)); //j
            temp4f[2] = vector_length[0];
            temp4f[3] = vector_length[1];
            bound_grids.push_back(temp4f);
        }
    } else {
        float grid_diagonal = grid_length * sqrt(2);
        // top left
        float x1 = _corner[l_i][0], x2 = _corner[t_i][0], y1 = _corner[l_i][1], y2 = _corner[t_i][1];
        for (int j = top[1]; j <= left[1]; j++) {
            for (int i = left[0]; i <= top[0]; i++) {
                if (i == left[0] && j == left[1]) {
                    continue;
                }
                grid_center[0] = i * grid_length + (grid_length / 2) - 1;
                grid_center[1] = (1 - j * grid_length) - (grid_length / 2);
                vector_length = grid_center - _pos;
                float dist = abs((x1 - grid_center[0]) * (y2 - grid_center[1]) - (x2 - grid_center[0]) * (y1 - grid_center[1])) / sqrt((x1 - x2) * (x1 - x2) + (y1 - y2) * (y1 - y2));
                // cout << "dist"<< dist << "diagonal/2" << grid_diagonal/2 << endl;
                if (dist <= grid_diagonal / 2) {
                    temp4f[0] = float(i + 1);			 //i
                    temp4f[1] = float(nGrid - (j + 1)); //j
                    temp4f[2] = vector_length[0];
                    temp4f[3] = vector_length[1];
                    bound_grids.push_back(temp4f);
                }
            }
        }
        //top right
        x1 = _corner[t_i][0];
        x2 = _corner[r_i][0];
        y1 = _corner[t_i][1];
        y2 = _corner[r_i][1];
        for (int j = top[1]; j <= right[1]; j++) {
            for (int i = top[0]; i <= right[0]; i++) {
                if (i == top[0] && j == top[1]) {
                    continue;
                }
                grid_center[0] = i * grid_length + (grid_length / 2) - 1;
                grid_center[1] = (1 - j * grid_length) - (grid_length / 2);
                vector_length = grid_center - _pos;
                float dist = abs((x1 - grid_center[0]) * (y2 - grid_center[1]) - (x2 - grid_center[0]) * (y1 - grid_center[1])) / sqrt((x1 - x2) * (x1 - x2) + (y1 - y2) * (y1 - y2));
                if (dist <= grid_diagonal / 2) {
                    temp4f[0] = float(i + 1);			 //i
                    temp4f[1] = float(nGrid - (j + 1)); //j
                    temp4f[2] = vector_length[0];
                    temp4f[3] = vector_length[1];
                    bound_grids.push_back(temp4f);
                }
            }
        }
        //bottom right
        x1 = _corner[r_i][0];
        x2 = _corner[b_i][0];
        y1 = _corner[r_i][1];
        y2 = _corner[b_i][1];
        for (int j = right[1]; j <= bottom[1]; j++) {
            for (int i = bottom[0]; i <= right[0]; i++) {
                if (i == right[0] && j == right[1]) {
                    continue;
                }
                grid_center[0] = i * grid_length + (grid_length / 2) - 1;
                grid_center[1] = (1 - j * grid_length) - (grid_length / 2);
                vector_length = grid_center - _pos;
                float dist = abs((x1 - grid_center[0]) * (y2 - grid_center[1]) - (x2 - grid_center[0]) * (y1 - grid_center[1])) / sqrt((x1 - x2) * (x1 - x2) + (y1 - y2) * (y1 - y2));
                // cout << "dist"<< dist << "diagonal/2" << grid_diagonal/2 << endl;
                if (dist <= grid_diagonal / 2) {
                    temp4f[0] = float(i + 1);			 //i
                    temp4f[1] = float(nGrid - (j + 1)); //j
                    temp4f[2] = vector_length[0];
                    temp4f[3] = vector_length[1];
                    bound_grids.push_back(temp4f);
                }
            }
        }
        //bottom left
        x1 = _corner[l_i][0];
        x2 = _corner[b_i][0];
        y1 = _corner[l_i][1];
        y2 = _corner[b_i][1];
        for (int j = left[1]; j <= bottom[1]; j++) {
            for (int i = left[0]; i <= bottom[0]; i++) {
                if (i == bottom[0] && j == bottom[1]) {
                    continue;
                }
                grid_center[0] = i * grid_length + (grid_length / 2) - 1;
                grid_center[1] = (1 - j * grid_length) - (grid_length / 2);
                vector_length = grid_center - _pos;
                float dist = abs((x1 - grid_center[0]) * (y2 - grid_center[1]) - (x2 - grid_center[0]) * (y1 - grid_center[1])) / sqrt((x1 - x2) * (x1 - x2) + (y1 - y2) * (y1 - y2));
                // cout << "dist"<< dist << "diagonal/2" << grid_diagonal/2 << endl;
                if (dist <= grid_diagonal / 2) {
                    temp4f[0] = float(i + 1);			 //i
                    temp4f[1] = float(nGrid - (j + 1)); //j
                    temp4f[2] = vector_length[0];
                    temp4f[3] = vector_length[1];
                    bound_grids.push_back(temp4f);
                }
            }
        }
    }
    return bound_grids;
}

bool compareVectors(Eigen::Vector2i g1, Eigen::Vector2i g2) {
    // sort by second entry
    return (g1[1] < g2[1]);
}

std::vector<Eigen::Vector2i> Particle::innerGrid(std::vector<Eigen::Vector4f> boundGrid4f)
{
    std::vector<Eigen::Vector2i> boundGrid;
    std::vector<Eigen::Vector2i> innerGrid;
    std::vector<int> rowGrid;
    Eigen::Vector2i temp;
    int dist;
    for (auto & i : boundGrid4f) {
        temp[0] = int(i[0]);
        temp[1] = int(i[1]);
        boundGrid.push_back(temp);
    }
    sort(boundGrid.begin(), boundGrid.end(), compareVectors);
    for (int i = 0; i < boundGrid.size() - 1; i++) {
        if (boundGrid.size() < 3) {
            break;
        }
        rowGrid.push_back(boundGrid[i][0]);
        if (boundGrid[i][1] != boundGrid[i + 1][1] || i == boundGrid.size() - 1) {
            if (i == boundGrid.size() - 1) {
                rowGrid.push_back(boundGrid[i + 1][0]);
            }
            sort(rowGrid.begin(), rowGrid.end());
            for (int j = 1; j < rowGrid.size(); j++) {
                dist = rowGrid[j] - rowGrid[j - 1];
                if (dist > 1) {
                    for (int k = 1; k < dist; k++) {
                        temp[0] = rowGrid[j - 1] + k;
                        temp[1] = boundGrid[i][1];
                        innerGrid.push_back(temp);
                    }
                }
            }
            std::vector<int>().swap(rowGrid);
        }
    }
    return innerGrid;
}

Eigen::Vector2i Particle::localGrid(int nGrid) {
    Eigen::Vector2i result;
    float grid_length = 2.0 / nGrid;
    result[0] = int((_pos[0] - (-1)) / grid_length) + 1;
    result[1] = int((1 - _pos[1]) / grid_length);
    result[1] = nGrid - (result[1] + 1);
    return result;
}

