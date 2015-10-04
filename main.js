/********************************************
 * Example of ray casting with a house
 * 
 * Use the mouse to move the scene
 * Use the left and right arrow keys
 * to move the camera
 * 
 * TODO Fixes
 *   Fix camera controls
 *   Fix ordering of elements
 *   Anti-aliasing (?)
 * 
 * TODO Features
 *   Make nice camera controls
 *   Camera zoom
 *   Control light intensity
 *   Control light position
 * 
 *   Create high resolution image
 * 
 *   Drag and drop pixel (?)
 *   Show pixel colours in grid (?)
 *
 *   Control to change scale of scene
 *   Different aspect ratio (?)
 *   
 *   Add details to house
*********************************************/

var BACKGROUND = color(100, 200, 250);
var SHADE = color(40, 40, 40);
var WHITE = color(255, 255, 255);

var RED = color(200, 0, 0);
var GREY = color(100, 100, 100);
var BLUE = color(64, 95, 237);
var PINK = color(255, 0, 175);
var GREEN = color(28, 173, 123);
var ORANGE = color(255, 165, 0);

var WALL_YELLOW = color(255, 255, 115);
var WALL_ORANGE = color(255, 175, 75);
var WALL_GREEN = color(220, 235, 16);
var WALL_PINK = color(255, 180, 200);
var WALL_BLUE = color(175, 195, 235);
var ROOF = color(190, 110, 88);
var BASE = color(80, 80, 80);
var DOOR = color(210, 45, 10);

var drawNodes = false;
var showImage = false;

var translateX = width - 250.5;
var translateY = height / 2 + 0.5;
var divider = 160;

var toolbarWidth = 144;
var toolbarHeight = 0;
var toolbarX = width * 0.01;
var toolbarY = width * 0.01;
var buttons = [];

var ambientInts = 0.3;

var showing = {
    Lights: true,
    Camera: true,
    'Camera direction': true,
    //'Image plane': true,
    'Pixel grid': true,
    //Pixel: true,
    'All rays': false,
    'Primary ray': true,
    'Shadow ray': false,
    'Reflected ray': false,
    Image: true,
};

/********************************************
 *      Linear algebra
*********************************************/

var addVectors = function(v1, v2) {
    return {
        x: v1.x + v2.x,
        y: v1.y + v2.y,
        z: v1.z + v2.z
    };
};

var subtractVectors = function(v1, v2){
    return {
        x: v1.x - v2.x,
        y: v1.y - v2.y,
        z: v1.z - v2.z
    };
};

var multiplyVector = function(v, s) {
    return {
        x: v.x * s,
        y: v.y * s,
        z: v.z * s
    };
};

var averageVectors = function(v1, v2) {
    return {
        x: (v1.x + v2.x) / 2,
        y: (v1.y + v2.y) / 2,
        z: (v1.z + v2.z) / 2
    };
};

var vectorLength = function(v) {
    return sqrt(v.x * v.x + v.y * v.y + v.z * v.z);
};

var normaliseVector = function(v) {
    var d = vectorLength(v);
    return { x: v.x / d, y: v.y / d, z: v.z / d };
};

// Starting at v1, go along to v2 by t
// t = 0, returns v1, t = 1, returns v2
var alongVectors = function(v1, v2, t) {
    var v3 = subtractVectors(v2, v1);
    return {
        x: v1.x + t * v3.x,
        y: v1.y + t * v3.y,
        z: v1.z + t * v3.z
    };
};

var dist3D = function(v1, v2) {
    var v = subtractVectors(v1, v2);
    return vectorLength(v);
};

var printVector = function(v) {
    println(v.x + " " + v.y + " " + v.z);
};

// Given a node, return a vector of its
// original coordinates
var originalNode = function(node) {
    return { x: node.sx, y: node.sy, z: node.sz };
};

// Assume vectors are 3D with attributes, x, y, z
var crossProduct = function(v1, v2) {
    return {
        x: v1.y * v2.z - v1.z * v2.y,
        y: v1.z * v2.x - v1.x * v2.z,
        z: v1.x * v2.y - v1.y * v2.x
    };
};

// Assume everything has 3 dimensions
var dotProduct = function(v1, v2){
    return v1.x * v2.x + v1.y * v2.y + v1.z * v2.z;
};

// Given at least 3 nodes, find the normal to the plane they define
// Only the first 3 nodes are used.
var normalOfPlane = function(nodes) {
    var edge1 = subtractVectors(nodes[0], nodes[1]);
    var edge2 = subtractVectors(nodes[0], nodes[2]);
    return crossProduct(edge1, edge2);
};

var multiplyMatrices = function(m1, m2) {
    var newMatrix = [];

    for (var i = 0; i < 3; i++) {
        var row = [];
        
        for (var j = 0; j < 3; j++) {
            var v = 0;
            
            for (var k = 0; k < 3; k++) {
                v += m1[i][k] * m2[k][j];
            }
            
            row.push(v);
        }
        
        newMatrix.push(row);
    }
    
    return newMatrix;
};

// Calculate whether a vector given by
// an origin and a direction,
// intersects with a triangle,
// given by 3 nodes/vectors
// From: http://en.wikipedia.org/wiki/M%C3%B6ller%E2%80%93Trumbore_intersection_algorithm
var triangleIntersection = function(vOrigin, vDirection, nodes) {
    var n1 = nodes[0];
    var n2 = nodes[1];
    var n3 = nodes[2];
    
    var edge1 = subtractVectors(n2, n1);
    var edge2 = subtractVectors(n3, n1);
    
    // Begin calculating determinant
    var p = crossProduct(vDirection, edge2);
    var det = dotProduct(edge1, p);
  
    // If determinant is near zero, ray lies in plane of triangle
    if (det > -EPSILON && det < EPSILON) { return 0;}
    var inv_det = 1 / det;
    
    // Calculate distance from V1 to ray origin
    var t = subtractVectors(vOrigin, n1);
 
    // Calculate u parameter and test bound
    var u = dotProduct(t, p) * inv_det;
    // The intersection lies outside of the triangle
    if (u < 0 || u > 1) { return 0; }
    
    // Prepare to test v parameter
    var q = crossProduct(t, edge1);
 
    // Calculate v parameter and test bound
    var v = dotProduct(vDirection, q) * inv_det;
    // The intersection lies outside of the triangle
    if (v < 0 || u + v > 1) { return 0; }
 
    var t = dotProduct(edge2, q) * inv_det;
 
    // Ray intersection
    // (length along direction from origin)
    if (t > EPSILON) { return t; }
};

var sortByZ = function(a, b) {
    return b.z - a.z;
};

var sortByPZ = function(a, b) {
    return b.pz - a.pz;
};

// Call update function for all elements in an array
var updateArray = function(arr) {
    for (var i = 0; i < arr.length; i++) {
        arr[i].update();
    }
};

/********************************************
 *      Rotate functions
*********************************************/

var rotateZ3D = function(nodes, theta) {
    var st = sin(theta);
    var ct = cos(theta);
    var x, y;
    
    for (var i = 0; i < nodes.length; i++) {
        x = nodes[i].x;
        y = nodes[i].y;
        nodes[i].x = ct * x - st * y;
        nodes[i].y = ct * y + st * x;
    }
};

var rotateY3D = function(nodes, theta) {
    var ct = cos(theta);
    var st = sin(theta);
    var x, z;

    for (var i = 0; i < nodes.length; i++) {
        x = nodes[i].x;
        z = nodes[i].z;
        nodes[i].x =  ct * x + st * z;
        nodes[i].z = -st * x + ct * z;
    }
};

var rotateX3D = function(nodes, theta){
    var ct = cos(theta);
    var st = sin(theta);
    var y, z;
    
    for (var i = 0; i < nodes.length; i++) {
        y = nodes[i].y;
        z = nodes[i].z;
        nodes[i].y = ct * y - st * z;
        nodes[i].z = st * y + ct * z;
    }
};

var getRotateXMatrix = function(theta) {
    var c = cos(theta);
    var s = sin(theta);
    return [[1, 0, 0], [0, c, -s], [0, s, c]];
};

var getRotateYMatrix = function(theta) {
    var c = cos(theta);
    var s = sin(theta);
    return [[c, 0, s], [0, 1, 0], [-s, 0, c]];
};

var applyMatrixToNodes = function(m, nodes) {
    for (var i = 0; i < nodes.length; i++) {
        var n = nodes[i];
        var x = n.x;
        var y = n.y;
        var z = n.z;
        n.x = m[0][0] * x + m[0][1] * y + m[0][2] * z;
        n.y = m[1][0] * x + m[1][1] * y + m[1][2] * z;
        n.z = m[2][0] * x + m[2][1] * y + m[2][2] * z;
    }
};

/********************************************
 *  GUI Button
*********************************************/

var Button = function(x, y, w, h, name, clickFunction) {
    this.x = x;
    this.y = y;
    this.w = w;
    this.h = h;
    this.name = name;
    this.defaultCol = color(220, 220, 220, 250);
    this.highlightCol = color(255, 255, 255, 240);
    this.showing = true;
    this.clickFunction = clickFunction;
};

Button.prototype.mouseOver = function() {
    return mouseX >= this.x &&
           mouseX <= this.x + this.w &&
           mouseY >= this.y &&
           mouseY <= this.y + this.h;
};

Button.prototype.click = function() {
    if (this.clickFunction) {
        this.clickFunction();
    }
};

Button.prototype.draw = function() {
    if (!this.showing) { return; }
    
    if (this.mouseOver() || this.selected) {
        fill(this.highlightCol);
    } else {
        fill(this.defaultCol);
    }
    strokeWeight(1);
    stroke(200);
    rect(this.x, this.y - 1, this.w, this.h + 3, 8);
    
    fill(10);
    textSize(15);
    textAlign(CENTER, CENTER);
    text(this.name, this.x + this.w / 2, this.y + this.h/2);
};

var CheckBox = function(x, y, w, h, name) {
    Button.call(this, x, y, w, h, name);
    this.box = this.h - 6;
    this.bx = this.x + 5;
    this.by = this.y + 3;
};
CheckBox.prototype = Object.create(Button.prototype);

CheckBox.prototype.click = function() {
    showing[this.name] = !showing[this.name];  
};

CheckBox.prototype.draw = function() {
    if (!this.showing) { return; }
    
    noStroke();
    if (this.mouseOver() || this.selected) {
        fill(this.highlightCol);
        rect(this.x, this.y, this.w, this.h + 1, 5);
    } else {
        noFill();
    }
    
    fill(10);
    textSize(14);
    textAlign(LEFT, CENTER);
    text(this.name, this.x + this.box + 9, this.y + this.h/2);
    
    noFill();
    stroke(10);
    strokeWeight(1);
    rect(this.bx, this.y + 3, this.box, this.box);
    
    if (showing[this.name]) {
        line(this.bx + 1, this.by + 1,
             this.bx + this.box, this.by + this.box);
        line(this.bx + this.box, this.by + 1, this.bx + 1, this.by + this.box);
    }
};

/**************************************
 *      Toolbar
 *  Contains other GUI elements
***************************************/

var Toolbar = function(x, y, w) {
    this.x = x;
    this.y = y;
    this.w = w;
    this.h = 0;
    
    this.buttons = [];
};

Toolbar.prototype.draw = function() {
    noStroke();
    fill(230, 230, 230, 200);
    rect(this.x, this.y, this.w, this.h, 8);
   
    for (var i = 0; i < this.buttons.length; i++) {
        this.buttons[i].draw();
    }
};

Toolbar.prototype.addOptions = function(options) {
    var x = this.x + 3;
    var y = this.y + 4;
    var w = this.w - 6;
    var h = 22;
    
    for (var opt in options) {
        this.buttons.push(new CheckBox(x, y, w, h, opt));
        y += 28;
    }
    
    this.h = y - 5;
};

Toolbar.prototype.mouseReleased = function() {
    var click = false;
    for (var i = 0; i < this.buttons.length; i++) {
        if (this.buttons[i].mouseOver() && this.buttons[i].selected) {
            this.buttons[i].click();
            click = true;
        }
        this.buttons[i].selected = false;
    }
    return click;
};

Toolbar.prototype.mousePressed = function() {
    for (var i = 0; i < this.buttons.length; i++) {
        if (this.buttons[i].mouseOver()) {
            this.buttons[i].selected = true;
        }
    }
};

/********************************************
 *      GUI Slider
*********************************************/

var Slider = function(x, y, width, min_v, max_v, current_v, name) {
    this.x = x;
    this.y = y;
    this.width = width;
    this.h = 12;
    this.held = false;
    this.name = name;
    
    this.ballR = 8;
    this.ballD = this.ballR * 2;
    
    this.min = min_v;
    this.max = max_v;
    this.scale = (max_v - min_v) / width;
    this.val = current_v === undefined ? min_v : current_v;
    this.bx = this.x + (this.val - min_v) / this.scale;
    
    this.held = false;
    this.showing = true;
};

Slider.prototype.draw = function() {
    noStroke();
    fill(180);
    rect(this.x-8, this.y - this.h/2, this.width + 16, this.h, 8);

    strokeWeight(1);
    stroke(0, 0, 0, 120);
    fill(180, 180, 250);
    ellipse(this.bx, this.y, this.ballD, this.ballD);
    noStroke();
    fill(255, 255, 255, 150);
    ellipse(this.bx - this.ballR * 0.3, this.y - this.ballR * 0.3, 5, 5);
};

Slider.prototype.mouseOver = function() {
    return dist(mouseX, mouseY, this.bx, this.y) < this.ballR;
};

Slider.prototype.mouseDragged = function() {
    var x = constrain(mouseX, this.x, this.x + this.width);
    this.bx = x;
    this.val = this.min + round((x - this.x) * this.scale);
};

// This is used if you want to update the value
// in a way other than using the slider
// (but want the slider to update).
Slider.prototype.update = function(d) {
    this.val = constrain(this.val + d, this.min, this.max);
    this.bx = (this.val - this.min) / this.scale + this.x;
};

/********************************************
 *      Node object
 * A node is an point in 3D space
*********************************************/

var Node = function(x, y, z, color) {
    // Initial value
    this.x = x;
    this.y = y;
    this.z = z;
    
    // Value after rotation
    this.px = x;
    this.py = y;
    this.pz = z;
    
    this.toDraw = (color !== undefined);
    this.r = 7;
    this.color = color || ORANGE;
};

Node.prototype.draw = function() {
    fill(this.color);
    noStroke();
    ellipse(this.px, this.py, this.r, this.r);
};

Node.prototype.update = function(persp, mat) {
    // Apply rotation
    this.px = mat[0][0] * this.x + 
              mat[0][1] * this.y +
              mat[0][2] * this.z;

    this.py = mat[1][0] * this.x + 
              mat[1][1] * this.y +
              mat[1][2] * this.z;

    this.pz = mat[2][0] * this.x + 
              mat[2][1] * this.y +
              mat[2][2] * this.z;
    
    // Apply perspective
    //var p = persp / (this.z + persp);
    //this.px *= p;
    //this.py *= p;
};

Node.prototype.getZ = function() {
    return this.pz;
};

Node.prototype.info = function() {
    println(this.x  + " " + this.y + " " + this.z);
};

// Convert an object with x, y, z attributes to node 
var toNode = function(p) {
    return new Node(p.x, p.y, p.z);
};
/*********************************************
 *      Edge object
 *  An edge is a line that join two nodes.
**********************************************/

var Edge = function(node1, node2, color, thickness) {
    this.node1 = node1;
    this.node2 = node2;
    this.update();
    this.color = color || WHITE;
    this.thickness = thickness || 1;
};

Edge.prototype.draw = function() {
    stroke(this.color);
    strokeWeight(this.thickness);
    line(this.x1, this.y1, this.x2, this.y2);
};

Edge.prototype.info = function() {
    println("Edge");
    this.node1.info();
    this.node2.info();
};

Edge.prototype.update = function() {
    // var dx = this.node1.x - this.node2.x;
    // var dy = this.node1.y - this.node2.y;
    // var theta = atan2(dx, dy);

    this.x1 = this.node1.px;
    this.y1 = this.node1.py;
    this.x2 = this.node2.px;
    this.y2 = this.node2.py;
    this.pz = 0.5 * (this.node1.pz + this.node2.pz);
};

Edge.prototype.getZ = function() {
    return min(this.node1.z, this.node2.z);
};

/*********************************************
 *      Face object
 * A face is a surface that joins
 * an array of nodes.
 * Its colour depends on its orientation
 * relative to a light source.
**********************************************/

var Face = function(nodes, color, reflection) {
    this.nodes = nodes;
    this.update();
    this.color = color || GREEN;
    this.light = this.color;
    this.reflection = reflection || 0;

    if (this.nodes.length === 3) {
        this.drawShape = this.triangle;
    } else {
        this.drawShape = this.quad;
    }
};

Face.prototype.update = function() {
    // Normal including rotation of scene
    // Used to determine order of parts
    this.normal = normaliseVector(
        crossProduct({
            x: this.nodes[0].px - this.nodes[1].px,
            y: this.nodes[0].py - this.nodes[1].py,
            z: this.nodes[0].pz - this.nodes[1].pz
        }, {
            x: this.nodes[0].px - this.nodes[2].px,
            y: this.nodes[0].py - this.nodes[2].py,
            z: this.nodes[0].pz - this.nodes[2].pz
        }
    ));
   
    // Find order in which to draw faces
    // by finding where it intersects the z-axis
    if (this.normal.z < 0) {
        this.pz = 0;
        var n = this.nodes.length;
        for (var i = 0; i < n; i++) {
            this.pz += this.nodes[i].pz;
        }
        this.pz /= n;
    } else {
        this.pz = null;
    }
};

Face.prototype.updateLights = function(lights) {
    // Normal, ignoring rotation of scene
    var normal = normaliseVector(normalOfPlane(this.nodes)); 
    
    var intensity = ambientInts;
    for (var i = 0; i < lights.length; i++) {
        intensity += lights[i].intensity * dotProduct(lights[i].normal, normal) / 2;    
    }
    
    intensity = constrain(intensity + ambientInts, ambientInts, 1);
    this.light = lerpColor(SHADE, this.color, intensity);
};

Face.prototype.info = function() {
    println("Face (" + this.nodes.length + ")");
    for (var i = 0; i < this.nodes.length; i++) {
        this.nodes[i].info();
    }
};

Face.prototype.draw = function() {
    strokeWeight(1);
    fill(this.light);
    stroke(this.light);
    this.drawShape();
};

Face.prototype.triangle = function() {
    triangle(this.nodes[0].px, this.nodes[0].py,
             this.nodes[1].px, this.nodes[1].py,
             this.nodes[2].px, this.nodes[2].py);
};

Face.prototype.quad = function() {
    quad(this.nodes[0].px, this.nodes[0].py,
         this.nodes[1].px, this.nodes[1].py,
         this.nodes[2].px, this.nodes[2].py,
         this.nodes[3].px, this.nodes[3].py);
};

/********************************************
 *      Light object
 * A position and a direction vector.
 * TODO: add intensity
*********************************************/

var Light = function(x1, y1, z1, x2, y2, z2, int) {
    this.intensity = int;
    this.nodes = [
        new Node(x1, y1, z1, WHITE),
        new Node(x2, y2, z2),
    ];
    
    this.getNormal();
    
    // Add node for display
    var len = -40 * this.intensity;
    this.nodes.push(new Node(
        this.nodes[0].x + len * this.normal.x,
        this.nodes[0].y + len * this.normal.y,
        this.nodes[0].z + len * this.normal.z
    ));
    
    this.edges = [
        new Edge(this.nodes[0], this.nodes[2])
    ];
};

Light.prototype.getNormal = function() {
    this.normal = normaliseVector(
        subtractVectors(
            this.nodes[0], this.nodes[1]
        )
    );
};

/********************************************
 *      Camera object
 * An (n x n) pixel screen of size, s,
 * at (x1, y1, z1), parallel to the screen.
 * The origin of light rays is d units away
 * out of the screen.
*********************************************/

var Camera = function(viewer, x, y, z, zoom, width, n) {
    this.viewer = viewer;
    this.zoom = zoom;
    this.n = n;
    this.numPixels = n * n;
    this.tileSize = width / this.n;
    
    this.angleX = 0;
    this.angleY = 0;
    
    this.nodes = [
        new Node(x, y, z - zoom, WHITE),
        new Node(x, y, z),
    ];
    
    // Red line from the camera to the image screen
    this.direction = new Edge(this.nodes[0], this.nodes[1], RED);
    
    this.grid = this.addScreen();
    this.rays = [];
    this.rayHits = [];
    
    // Pixel grid
    this.x1 = 12;
    this.y1 = height - width - 75;
    this.gridSize = width;
    this.x2 = this.x1 + this.gridSize;
    this.y2 = this.y1 + this.gridSize;
    this.px = 0;
    this.py = 0;
};

// Add a grid of pixels
Camera.prototype.addScreen = function() {
    var n = this.n;
    var n1 = n + 1;
    var n2 = n / 2;
    var base = this.nodes[1];
    var edges = [];
    
    // Add nodes
    for (var i = 0; i <= this.n; i++) {
        var x = (i - n2) * this.tileSize;
        
        for (var j = 0; j <= this.n; j++) {
            var y = (j - n2) * this.tileSize;
            
            this.nodes.push(new Node(
                base.x + x,
                base.y + y,
                base.z
            ));
        }
    }
    
    // Add edges to form pixels
    for (var i = 0; i < n1; i++) {
        for (var j = 0; j < n1; j++) {
            var p = j * n1 + i + 2;
            var node = this.nodes[p];
            
            if (i > 0) {
                edges.push(
                    new Edge(node, this.nodes[p - 1]
                ));   
            }
            
            if (j > 0) {
                edges.push(
                    new Edge(node, this.nodes[p - n - 1])
                );   
            }
        }
    }
    
    // Add edges to form border
    var ns = [2, 2 + n, n1 * n1 + 1, n1 * n + 2];
    for (var i = 0; i < 4; i++) {
        edges.push(new Edge(
            this.nodes[ns[i]], this.nodes[ns[(i + 1) % 4]],
            WHITE, 2
        ));
    }
    
    return edges;
};

// Add rays from the camera node
// through each pixel
Camera.prototype.addRays = function() {
    this.rays = [];
    this.rayHits = [];
    this.shadowRays = {};
    this.reflectedRays = {};
    this.colors = [];
    
    var n1 = this.n + 1;
    var i = 0;
    
    for (var x = 0; x < this.n; x++) {
        var row = [];
        
        for (var y = 0; y < this.n; y++) {
            // Get vector to center of pixel
            var n2 = x * n1 + y + 2;
            var pixel = averageVectors(
                this.nodes[n2],
                this.nodes[n1 + n2 + 1]
            );
            
            var col = this.getPixelColor(pixel, i);
            row.push(col);
            
            // Add ray of the right colour
            col = lerpColor(col, WHITE, 0.3);
            this.rays.push(new Edge(
                this.nodes[0],
                this.rayHits[i],
                col, 2
            ));
            i++;
        }
        
        this.colors.push(row);
    }
    
    // Create selected ray
    this.ray = new Edge(
        this.nodes[0], this.rayHits[0], PINK, 2
    );
};

Camera.prototype.getPixelColor = function(pixel, i) {
    // Find what the ray hits
    var dir = normaliseVector(
        subtractVectors(pixel, this.nodes[0]));
    var ray = this.viewer.rayIntersection(this.nodes[0], dir);
    
    // Add end point of ray, either in space
    // or where it hits an object
    this.rayHits.push(toNode(ray.point));
    
    // Figure out colour of ray and pixel
    var col = BACKGROUND;
    
    if (ray.face) {
        var light = this.viewer.lights[0];
        
        // Find pixel intensity
        var int = 0;
        var away = true;
        
        // If face faces away from light
        // then it is in shadow
        if (dotProduct(ray.face.normal, light.normal) > 0) {
            away = false;
            int = this.viewer.rayCollision(ray.point, light);
        }
        
        var p = ambientInts + int * (1 - ambientInts);
        col = lerpColor(SHADE, ray.face.light, p);
        
        // If in shadow, show ray to nearest point
        if (!away && !int) {
            var lightDir = normaliseVector(
                subtractVectors(
                    light.nodes[0], ray.point
                )
            );
            
            var hit = this.viewer.rayIntersection(ray.point, lightDir);
            // Where the ray tp the light 
            // hits another object
            var shadowNode = toNode(hit.point);
            this.nodes.push(shadowNode);
            
            // Add end point of ray
            this.shadowRays[i] = new Edge(
                shadowNode, this.rayHits[i],
                GREY, 2);
        } else {
            // Add end point of ray
            this.shadowRays[i] = new Edge(
                light.nodes[0], this.rayHits[i],
                WHITE, 2
            );
        }
        
        // Find reflection
        if (ray.face.reflection) {
            var reflectedColor = this.reflection(ray, dir, i);
            col = lerpColor(col, reflectedColor, 0.4);
        }
        
        return col;
    } else {
        return false;
    }
};

Camera.prototype.reflection = function(ray, dir, i) {
    var dp = dotProduct(dir, ray.face.normal);
    var reflection = normaliseVector(
        subtractVectors(
            dir,
            multiplyVector(ray.face.normal, 2 * dp)));
            
    var hit = this.viewer.rayIntersection(
        ray.point, reflection, 160);
    
    var reflectedColor;
    if (hit.face) {
        reflectedColor = hit.face.light;
    } else {
        reflectedColor = BACKGROUND;
    }
    
    var reflectNode = toNode(hit.point);
    this.nodes.push(reflectNode);
    
    // Add end point of ray
    this.reflectedRays[i] = new Edge(
        reflectNode,
        this.rayHits[i],
        PINK + (80 << 24), 2
    );
    
    return reflectedColor;
};

Camera.prototype.updateRays = function() {
    var n1 = this.n + 1;
    var i = 0;
    
    for (var x = 0; x < this.n; x++) {
        for (var y = 0; y < this.n; y++) {
            var n2 = x * n1 + y + 2;
            var pixel = averageVectors(
                this.nodes[n2],
                this.nodes[n1 + n2 + 1]
            );
            
            var dir = normaliseVector(subtractVectors(pixel, this.nodes[0]));
            var hit = this.viewer.rayIntersection(this.nodes[0], dir);
            var end = this.rayHits[i];
            end.x = hit.point.x;
            end.y = hit.point.y;
            end.z = hit.point.z;
        
            var col = BACKGROUND;
            if (hit.face) {
                col = hit.face.light;
                this.colors[x][y] = col;
            } else {
                this.colors[x][y] = false;
            }
            
            col = lerpColor(col, WHITE, 0.3);
            this.rays[i].color = col;
            i++;
        }
    }
};

Camera.prototype.update = function(persp, mat) {
    for (var i = 0; i < this.nodes.length; i++) {
        this.nodes[i].update(persp, mat);
    }
    
    this.direction.update();
    updateArray(this.grid);
    
    for (var i = 0; i < this.rayHits.length; i++) {
        this.rayHits[i].update(persp, mat);
    }
    
    updateArray(this.rays);
    
    if (this.ray) {
        this.ray.update();
    }
    
    if (this.shadowRay) {
        this.shadowRay.update();
    }
    
    if (this.reflectedRay) {
        this.reflectedRay.update();
    }
};

// Draw a 2D version of the grid
Camera.prototype.drawPixels = function() {
    var d = this.gridSize / this.n;

    strokeWeight(1);
    stroke(WHITE);
    fill(BACKGROUND);
    rect(this.x1 - 1, this.y1 -1, this.n * d + 2, this.n * d + 2);

    if (this.colors) {
        noStroke();
        for (var x = 0; x < this.n; x++) {
            for (var y = 0; y < this.n; y++) {
                if (this.colors[x][y]) {
                    fill(this.colors[x][y]);
                    var x1 = this.x1 + x * d;
                    var y1 = this.y1 + y * d;
                    rect(x1, y1, d, d);
                }
            }
        }
    }
    
    // Pixel outlines
    if (showing['Pixel grid']) {
        noFill();
        strokeWeight(1);
        stroke(WHITE);
        
        for (var i = 0; i <= this.n; i++) {
            var x = this.x1 + i * d;
            var y = this.y1 + i * d;
            line(x, this.y1, x, this.y2);
            line(this.x1, y, this.x2, y);
        }    
    }

    // Highlighted pixel
    if (showing.Ray) {
        var x = map(this.px, 0, this.n, this.x1, this.x2);
        var y = map(this.py, 0, this.n, this.y1, this.y2);
        
        fill(255, 0, 175, 200);
        rect(x, y, d, d);
    }
};

Camera.prototype.selectPixel = function() {
    if (mouseX > divider) { return; }
    
    if (!(mouseX > this.x1 && mouseX < this.x2 &&
          mouseY > this.y1 && mouseY < this.y2)) {
              return;
    }
    
    var x = floor(map(mouseX, this.x1, this.x2, 0, this.n));
    var y = floor(map(mouseY, this.y1, this.y2, 0, this.n));
    
    var n = x * this.n + y;
    this.ray.node2 = this.rays[n].node2;
    this.shadowRay = this.shadowRays[n];
    this.reflectedRay = this.reflectedRays[n];
    
    if (x !== this.px || y !== this.py) {
        this.px = x;
        this.py = y;
        this.viewer.collectParts();
    }
};

Camera.prototype.setZoom = function(zoom) {
    this.zoom = zoom;
    var dir = normaliseVector(subtractVectors(this.nodes[0], this.nodes[1]));
    
    this.nodes[0].x = this.nodes[1].x + zoom * dir.x;
    this.nodes[0].y = this.nodes[1].y + zoom * dir.y;
    this.nodes[0].z = this.nodes[1].z + zoom * dir.z;
};

/*********************************************
 *      Viewer object
 * Consists of a camera object and a scene.
 * Allows both to be rotated and shows rays
 * from the camera intersecting with the scene.
**********************************************/

var Viewer = function(lights, scene) {
    // Add Scene
    this.scene = scene;
    
    // Add lights
    this.lights = lights;
    this.updateLights();
    
    // Create camera
    this.camera = new Camera(
        this, 0, 0, -120, 120, 112, 16
    );
    
    // Get initial scene
    this.perspective = 1000;
    this.matrix = [[1, 0, 0], [0, 1, 0], [0, 0, 1]];
    this.objects = this.lights.concat([scene]);
    this.collectParts();
    
    // Add camera rays
    this.camera.addRays();
    this.collectParts();
};

Viewer.prototype.update = function() {
    for (var i = 0; i < this.objects.length; i++) {
        this.updateObject(this.objects[i]);    
    }
    this.camera.update(this.perspective, this.matrix);
    this.parts.sort(sortByPZ);
};

Viewer.prototype.updateObject = function(obj) {
    var nodes = obj.nodes;
    var faces = obj.faces;

    for (var i = 0; i < nodes.length; i++){
        nodes[i].update(this.perspective, this.matrix);
    }

    if (obj.edges) { updateArray(obj.edges); }
    if (obj.faces) { updateArray(obj.faces); }
};

Viewer.prototype.updateLights = function() {
    var faces = this.scene.faces;
    
    for (var j = 0; j < faces.length; j++) {
        faces[j].updateLights(this.lights);
    }

};

Viewer.prototype.draw = function() {
    if (!showImage) {
        pushMatrix();
        translate(translateX, translateY);
        
        for (var i = 0; i < this.parts.length; i++) {
            if (this.parts[i].z !== null) {
                this.parts[i].draw();   
            }
        }
        
        popMatrix();
        
        if (showing.Image) {
            this.camera.drawPixels();    
        }
    } else if (this.rayCast){
        var oldCol, newCol;
        var newRow = [];

        strokeWeight(1);
        for (var i = 0; i < this.rayS; i++) {
            var newCol = this.castRay();
            
            if (i > 0) {
                //newRow.push(lerpColor(newCol, oldCol, 0.5));           
                stroke(lerpColor(newCol, oldCol, 0.5));
                point(i + 160, 70 + this.rayY);
            }
            oldCol = newCol;
        }
        
        // Anti-aliased ray tracing
        /*
        if (this.rayY > 0) {
            for (var i = 0; i < newRow.length; i++) {
                stroke(lerpColor(newRow[i], this.oldRow[i], 0.5));
                point(i + 5, this.rayY + 200);
            }
        }
        this.oldRow = newRow;
        */
    }
};

Viewer.prototype.mouseDragged = function() {
    var d = 0.4;
    var dx = -d * (mouseX - pmouseX);
    var dy = d * (mouseY - pmouseY);
    
    var m = [[1, 0, 0], [0, 1, 0], [0, 0, 1]];
    
    if (dx) {
        m = getRotateYMatrix(dx);
    }
    
    if (dy) {
        m = multiplyMatrices(getRotateXMatrix(dy), m);
    }
    
    if (dx || dy) {
        this.matrix = multiplyMatrices(m, this.matrix);
    }
    
    this.collectParts();
};

Viewer.prototype.moveCamera = function(sliders) {
    var angleX = sliders[0].val;
    var angleY = sliders[1].val;
    var zoom = sliders[2].val;
    var dx = angleX - this.camera.angleX;
    
    var m = getRotateXMatrix(-this.camera.angleY);
    
    if (dx !== 0) {
        m = multiplyMatrices(m, getRotateYMatrix(dx));
    }
    
    if (angleY !== 0) {
        m = multiplyMatrices(m, getRotateXMatrix(angleY));
    }
    
    if (dx !== 0 || angleY !== 0) {
        // Update the camera position
        applyMatrixToNodes(m, this.camera.nodes);
        this.camera.angleX = angleX;
        this.camera.angleY = angleY;
    }
    
    // Add new rays
    this.camera.updateRays();
    
    // Reorders everything as needed
    this.collectParts();  
};

Viewer.prototype.collectParts = function() {
    this.parts = [];
    
    // Add scene nodes and faces
    if (drawNodes) {
        this.parts = this.parts.concat(this.scene.nodes);
    }
    
    // Add object
    for (var i = 0; i < this.scene.faces.length; i++) {
        var face = this.scene.faces[i];
        if (!face.hide && face.pz !== null) {
            this.parts.push(face);
        }
    }

    if (showing.Lights) {
        for (var i = 0; i < this.lights.length; i++) {
            this.parts.push(this.lights[i].nodes[0]);
            this.parts.push(this.lights[i].edges[0]);   
        }
    }
    
    if (showing.Camera) {
        this.parts.push(this.camera.nodes[0]);
    }
    
    if (showing['Camera direction']) {
        this.parts.push(this.camera.direction);
    }
    
    if (showing['Primary ray']) {
        this.parts.push(this.camera.ray);
    }
    
    if (showing['Shadow ray'] && this.camera.shadowRay) {
        this.parts.push(this.camera.shadowRay);
    }
    
    if (showing['Reflected ray'] && this.camera.reflectedRay) {
        this.parts.push(this.camera.reflectedRay);
    }
    
    if (showing['Refracted ray'] && this.camera.refractedRay) {
        this.parts = this.parts.concat(this.camera.refractedRay);
    }
    
    if (showing['All rays']) {
        this.parts = this.parts.concat(this.camera.rays);
    }
    
    if (showing['Pixel grid']) {
        this.parts = this.parts.concat(this.camera.grid);
    }
    
    this.update();
};

Viewer.prototype.startRayCast = function(s) {
    this.rayX = 0;
    this.rayY = 0;
    this.rayS = s;
    this.rayCast = true;
    this.oldRow = [];
    showImage = true;
    
    noFill();
    stroke(255);
    strokeWeight(1);
    rect(159, 69, s + 2, s + 2);
    
    this.camOrigin = this.camera.nodes[2];
    var camMaxY = this.camera.nodes[2 + this.camera.n];
    var camMaxX = this.camera.nodes[2 + this.camera.n + this.camera.numPixels];
    this.rayDx = subtractVectors(camMaxX, this.camOrigin);
    this.rayDy = subtractVectors(camMaxY, this.camOrigin);
};

Viewer.prototype.castRay = function() {
    var dx = multiplyVector(this.rayDx, this.rayX / this.rayS);
    var dy = multiplyVector(this.rayDy, this.rayY / this.rayS);
    var pixel = addVectors(this.camOrigin, addVectors(dx, dy));
    
    var dir = normaliseVector(subtractVectors(pixel, this.camera.nodes[0]));
    var hit = this.rayintersection(pixel, dir);
    
    this.rayX++;
    if (this.rayX >= this.rayS) {
        this.rayX = 0;
        this.rayY++;
        if (this.rayY > this.rayS) {
            this.rayCast = false;
        }
    }
    
    if (!hit.face) { return BACKGROUND; }

    // Check whether point is in shadow
    var p = ambientInts;
    for (var i = 0; i < this.lights.length; i++) {
        p += this.rayCollision(hit.point, this.lights[i]);    
    }
    
    return lerpColor(SHADE, hit.face.light, min(1, p));

};

Viewer.prototype.rayIntersection = function(origin, dir, minDist, flip) {
    minDist = minDist || 550;
    flip = flip || 1;
    var targetFace = false;
    
    for (var f = 0; f < this.scene.faces.length; f++) {
        var face = this.scene.faces[f];
        if (flip * dotProduct(face.normal, dir) < 0) {
            var d = triangleIntersection(origin, dir, face.nodes);
            
            if (d > 0 && d < minDist) {
                minDist = d;
                targetFace = face;
            }
        }
    }
    
    dir = multiplyVector(dir, minDist);

    return {
        face: targetFace,
        point: addVectors (origin, dir)
    };
};

// Test intesection of ray from origin to target
// with any face. Return true if any intersection
Viewer.prototype.rayCollision = function(origin, light) {
    var target = light.nodes[0];
    // Vector in direction of ray
    var dir = normaliseVector(subtractVectors(target, origin));
    
    var d = subtractVectors(origin, target);
    var len = dotProduct(d, d);
    var p = light.intensity * 400000 / (400000 + len);
    
    for (var f = 0; f < this.scene.faces.length; f++) {
        var face = this.scene.faces[f];
        var d = triangleIntersection(origin, dir, face.nodes);
        
        if (d > 0) { return 0; }
    }
    
    return p;
};


/********************************************
 *      Create objects
*********************************************/

var createFaceObjects = function(nodeIds, nodes, col) {
    var faces = [];
    
    for (var f = 0; f < nodeIds.length; f++) {
        var face = nodeIds[f];
        faces.push(
            new Face(
                [
                    nodes[face[0]],
                    nodes[face[1]],
                    nodes[face[2]]
                ],
                col
            )
        );
    }
    
    return faces;
};

var addFaces = function(ids, nodes, faces, col, refl) {
    for (var i = 0; i < ids.length; i++) {
        var face = ids[i];
        var n1 = nodes[face[0]];
        
        for (var f = 1; f < face.length - 1; f++) {
            var n2 = nodes[face[f]];
            var n3 = nodes[face[f + 1]];
            faces.push(
                new Face([n1, n2, n3], col, refl)
            );
        }
    }
};

var createHouse = function(s) {
    var reflection = 0;
    var nodes = [];
    var faces = [];
    
    // Depth
    var d = 150;
    // Depth step for left side, front
    var d2 = 24;
    // Depth of porch
    var d3 = 30;
    // Depth step for left side, back
    var d4 = d - 15;
    // Inset for right front part
    var d5 = 15;
    
    var j = 60 + 32 * 0.8;
    
    var cx = 124 / 2;
    var cy = 135 / 2;
    var cz = d / 2;
    
    var coords = [
        // Front step
        [0, 0, d2], [60, 0, d2],
        [60, 5, d2], [0, 5, d2],
        
        // Inset front
        [0, 5, d2 + d3], [60, 4, d2 + d3],
        [60, 45, d2 + d3], [0, 45, d2 + d3],
        
        // Porch top
        [0, 45, d2], [60, 45, d2],
        [60, 60, d2], [0, 60, d2],
        
        // Front wall, right
        [60 + d5, 0, 0], [124 - d5, 0, 0],
        [124, 0, d2], [124, 60, d2],
        [124 - d5, 60, 0], [60 + d5, 60, 0],
        [60, 60, 0], [124, 60, 0],
        
        // Back wall, left
        [60, 0, d4], [0, 0, d4],
        [0, 60, d4], [60, 60, d4],
        
        // Back wall, right
        [124, 0, d], [60, 0, d],
        [60, 60, d], [124, 60, d],
        
        // Left roof
        [0, 120, d / 2], [j, 120, d / 2],

        // Right roof
        [92, 135, 0], [92, 135, d],
    ];
    
    for (var i = 0; i < coords.length; i++) {
        var node = coords[i];
        nodes.push(
            new Node(
                (node[0] - cx) * s,
                (cy - node[1]) * s,
                (node[2] - cz) * s
        ));
    }
    
    // Front step
    addFaces([
        [0, 1, 2, 3], [3, 2, 5, 4]],
        nodes, faces, WALL_PINK, reflection);
    
    // Inset front
    addFaces([[4, 5, 6, 7]],
             nodes, faces, WALL_ORANGE, reflection);
    
    // Front right underhang
    addFaces([[10, 17, 18], [15, 19, 16]],
             nodes, faces, WALL_ORANGE, reflection);
    
    // Porch top
    addFaces([
        [8, 9, 10, 11], [7, 6, 9, 8]],
        nodes, faces, WALL_BLUE, reflection);
    
    // Front wall, right
    addFaces([
        [1, 12, 17, 10], [12, 13, 16, 17],
        [13, 14, 15, 16], [5, 2, 9, 6]
        ], nodes, faces, WALL_GREEN, reflection);
    
    // Right gables
    addFaces([[18, 19, 30], [27, 26, 31]],
             nodes, faces, WALL_YELLOW, reflection);
    
    // Left side
    addFaces([
        [0, 3, 4], [0, 4, 21], [4, 7, 21],
        [7, 22, 21], [7, 8, 11], [7, 11, 22],
        [22, 11, 28]
        ], nodes, faces, WALL_ORANGE, reflection);

    // Right wall
    addFaces([[14, 24, 27, 15]],
             nodes, faces, WALL_PINK, reflection);
 
    // Back wall, left
    addFaces([[20, 21, 22, 23]],
             nodes, faces, WALL_ORANGE, reflection);
      
    // Back wall, right
    addFaces([
        [24, 25, 26, 27], [20, 23, 26, 25]
        ], nodes, faces, WALL_GREEN, reflection);
   
    // Roof
    addFaces([
        // Left
        [11, 10, 29, 28], [23, 22, 28, 29],
        // Join
        [10, 18, 30], [10, 30, 29],
        [26, 23, 31], [23, 29, 31],
        [29, 30, 31],
        // Right
        [19, 27, 31, 30]
        ], nodes, faces, ROOF, reflection);
        
    // Base
    addFaces([
        [0, 21, 20, 1], [25, 24, 14, 1],
        [1, 14, 13, 12]
        ], nodes, faces, BASE, reflection);
    
    return { nodes: nodes, faces: faces };
};

// Create the light, camera and scene
var myLights = [
    new Light(40, -80, -120, 0, 0, 0, 0.7),
    new Light(-160, -10, -50, 0, 0, 0, 0.25),
];
var house = createHouse(1);
var viewer = new Viewer(myLights, house);

// Create Toolbar
var toolbar = new Toolbar(toolbarX, toolbarY, toolbarWidth, toolbarHeight);
toolbar.addOptions(showing);

var selected = false;
var sliders = [
    new Slider(16, height - 60, 120, 0, 360, 0, "Camera yaw"),
    new Slider(16, height - 40, 120, -90, 90, 0, "Camera pitch"),
   // new Slider(16, height - 40, 120, 40, 280, 120, "Zoom"),
];
var rayCastButton = new Button(11, height - 26, 130, 19, "Start Ray Casting");

/********************************************
 *      Main loop
*********************************************/

background(BACKGROUND);

draw = function() {
    if (showImage) {
        noStroke();
        fill(BACKGROUND);
        //rect(0, 0, width, 198);
        //rect(210, 0, width, height);   
    } else {
        background(BACKGROUND);
    }
    
    viewer.draw();
    toolbar.draw();
    
    for (var i = 0; i < sliders.length; i++) {
        sliders[i].draw();
    }
    rayCastButton.draw();
};

/********************************************
 *      Event handling
*********************************************/

mousePressed = function() {
    if (showing.Image) {
        viewer.camera.selectPixel();
    }
    toolbar.mousePressed();
    showImage = false;
    
    for (var i = 0; i < sliders.length; i++) {
        if (sliders[i].mouseOver()) {
            selected = sliders[i];
        }
    } 
};

mouseDragged = function() {
    if (mouseX > divider) {
        viewer.mouseDragged();    
    } else {
        //viewer.camera.selectPixel();
    }
    if (selected) {
        selected.mouseDragged();
        viewer.moveCamera(sliders);
    }
};

mouseReleased = function() {
    if (toolbar.mouseReleased()) {
        viewer.collectParts();
    }
    selected= false;
    if (rayCastButton.mouseOver()) {
        viewer.startRayCast(400);
    }
};

mouseOut = function() {
    mouseReleased();
};

keyPressed = function() {
    if (keyCode === LEFT) {
        // viewer.moveCamera(4);
    } else if (keyCode === RIGHT) {
        // viewer.moveCamera(-4);
    } else if (keyCode === 81) {
        viewer.startRayCast(16);
    }
    
};
