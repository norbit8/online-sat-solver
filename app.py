from flask import Flask, send_from_directory
from datetime import datetime
from Parser import *

app = Flask(__name__)

@app.route('/')
def homepage():
    the_time = datetime.now().strftime("%A, %d %b %Y %l:%M %p")
    cnf, variables, phi = parse('(p3->p2)')
    return """
    <h1>Hello heroku</h1>
    <p>(p3->p2) in cnf is {the_cnf}.</p>
    """.format(the_cnf=cnf)

@app.route('/yoav')
def bruh():
    the_time = datetime.now().strftime("%A, %d %b %Y %l:%M %p")
    cnf, variables, phi = parse('(p3->p2)')
    return send_from_directory('/templates', 'index.html')

if __name__ == '__main__':
    app.run(debug=True, use_reloader=True)


