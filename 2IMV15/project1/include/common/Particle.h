#pragma once

#include <cassert>
#include <gfx/vec2.h>

class Particle
{
private:
	Vec2f _initPos;
	Vec2f _pos;
	Vec2f _v;
	Vec2f _f;
	double _m;

    int _ind;
public:
	Particle(const Vec2f &ConstructPos, double m, int ind);
	virtual ~Particle();

	Vec2f initPos() { return _initPos; }
	Vec2f pos() { return _pos; }
	float pos(int i) {
		assert(i == 0 || i == 1);
		return _pos[i];
	}
	Vec2f v() { return _v; }
	float v(int i) {
		assert(i == 0 || i == 1);
		return _v[i];
	}
	Vec2f f() { return _f; }
	float f(int i) {
		assert(i == 0 || i == 1);
		return _f[i];
	}
	double m() const { return _m; }
    int ind() const { return _ind; }

	void setPos(const Vec2f &pos) { _pos = pos; }
	void setPos(const float &pos, int i) { _pos[i] = pos; }
    void setV(const Vec2f &v) { _v = v; }
    void setV(const float &v, int i) { _v[i] = v; }
	void setF(const Vec2f &f) { _f = f; }
    void setF(const float &f, int i) { _f[i] = f; }

    void updatePos(const Vec2f &pos) { _pos += pos; }
    void updateV(const Vec2f &v) { _v += v; }
    void updateF(const Vec2f &f) { _f += f; }
    void updateF(float &f, int i) { _f[i] += f; }

	void reset();
	void draw();
};
