#pragma once

#include <cassert>
#include <gfx/vec2.h>
#include <vector>
#include "eigen/Core"

enum PTYPE {
    RIGID,
    FIX,
    MOVING,
    NORMAL
};

class Particle
{
private:
	Eigen::Vector2f _initPos;
	Eigen::Vector2f _pos;
	Eigen::Vector2f _v;
	Eigen::Vector2f _f;
	double _m;
    PTYPE _pType;

    std::vector<Eigen::Vector2f> _corner; // for rotation positions from mass center
    Eigen::Vector2f _massCenter;
    float _dimension = 0.2;
    float _inertia;
    double _totalMass;
    // state
    Eigen::Vector2f _lm; // linear momentum P(t)
    float _angle;        // rotation R(t)
    float _am;           // angular momentum L(t)
    float _omega;        // angular velocity omega(t)
    float _torque;       // I*w'
    Eigen::MatrixXf _r;  // rotation R(t)

    int _ind;
public:
	Particle(const Eigen::Vector2f &constructPos, double m, int ind, PTYPE pType);
	virtual ~Particle();

	Eigen::Vector2f initPos() { return _initPos; }
	Eigen::Vector2f pos() { return _pos; }
	float pos(int i) {
		assert(i == 0 || i == 1);
		return _pos[i];
	}
	Eigen::Vector2f v() { return _v; }
	float v(int i) {
		assert(i == 0 || i == 1);
		return _v[i];
	}
	Eigen::Vector2f f() { return _f; }
	float f(int i) {
		assert(i == 0 || i == 1);
		return _f[i];
	}
    PTYPE type() { return _pType; }
	double m() const { return _m; }
    Eigen::Vector2f lm() { return _lm; }
    int ind() const { return _ind; }
    float am() const { return _am; }
    float angle() const { return _angle; }
    float omega() const { return _omega; }
    float inertia() const { return _inertia; }
    float torque() const { return _torque; }
    float dimension() const { return _dimension; }
    Eigen::Vector2f massCenter() { return _massCenter; }
    std::vector<Eigen::Vector2f> boundBox() { return _corner; }
    Eigen::Vector2f boundBox(int i) { return _corner[i]; }
    Eigen::MatrixXf r() { return _r; }

    static float minDistance(const Eigen::Vector2f& p1, const Eigen::Vector2f& p2, const Eigen::Vector2f& p3) {
        Eigen::Vector2f e12 = p2 - p1, e23 = p3 - p2, e13 = p3 - p1;
        float d23 = e12.dot(e23), d13 = e12.dot(e13), minDist;
        if (d23 > 0) {
            minDist = e23.norm();
        } else if (d13 < 0) {
            minDist = e13.norm();
        } else {
            float mod = e12.norm();
            minDist = std::abs(e12[0] * e13[1] - e12[1] * e13[0]) / mod;
        }
        return minDist;
    }

	void setPos(const Eigen::Vector2f &pos) { _pos = pos; }
	void setPos(const float &pos, int i) { _pos[i] = pos; }
    void setV(const Eigen::Vector2f &v) { _v = v; }
    void setV(const float &v, int i) { _v[i] = v; }
	void setF(const Eigen::Vector2f &f) { _f = f; }
    void setF(const float &f, int i) { _f[i] = f; }
    void setBoundBox(const Eigen::Vector2f& m, int i) { _corner[i] = m; }
    void setMassCenter(float m1, float m2) {
        _massCenter[0] = m1;
        _massCenter[1] = m2;
    }
    void setLM(float m1, float m2) {
        _lm[0] = m1;
        _lm[1] = m2;
    }
    void setAngle(float a) {
        _angle = a;
    }
    void setAM(float a) {
        _am = a;
    }
    void setR(int i, int j, float r) {
        _r(i, j) = r;
    }
    void setOmega(float o) {
        _omega = o;
    }
    void setInertia(float i) {
        _inertia = i;
    }
    void setTorque(float t) {
        _torque = t;
    }

    void updatePos(const Eigen::Vector2f &pos) { _pos += pos; }
    void updateV(const Eigen::Vector2f &v) { _v += v; }
    void updateF(const Eigen::Vector2f &f) { _f += f; }
    void updateF(float &f, int i) { _f[i] += f; }
    void updateTorque(float t) { _torque += t; }
    void updateBoundBox(const Eigen::Vector2f& m, int i) { _corner[i] += m; }

	void reset();
	void draw();
    void setBoundBox();
    std::vector<Eigen::Vector2f> getClosestEdge(const Eigen::Vector2f& point);
    std::vector<Eigen::Vector4f> boundGrid(int nGrid);
    std::vector<Eigen::Vector2i> innerGrid(std::vector<Eigen::Vector4f> boundGrid4f);
    Eigen::Vector2i localGrid(int nGrid);
};
