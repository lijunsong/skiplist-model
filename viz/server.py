from flask import render_template
from flask import Flask
from flask import request
from flask import abort, redirect, url_for
import os.path

app = Flask(__name__)
app.debug = True

@app.route('/')
def viz():
    return render_template('viz.html');

@app.route('/data.txt')
def request_data():
    contents = ''
    with open('data.txt') as f:
        contents = f.read()
    return contents

@app.route('/save', methods=['POST'])
def save():
    text = request.form['input-text']
    if text.strip() != u"":
        with open('data.txt', 'w') as f:
            f.write(text)
    return redirect(url_for('viz'))

if __name__ == '__main__':
    app.run()
